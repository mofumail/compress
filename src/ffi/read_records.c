// The common block below is repeated in read_arrays.c, read_blob_arrays.c,
// read_records.c and write_arrays.c under one guard, so each effect also
// compiles alone.
#ifndef BZ_ARRAYS_COMMON
#define BZ_ARRAYS_COMMON

#include <pthread.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>

// Array I/O for the fast path. A chunk is an Array<U32> holding its bytes
// packed four per slot, little-endian -- i.e. the bytes themselves, in
// memory order -- with the byte count in the LAST slot. So a chunk is read
// with one pread straight into its block and written with one pwrite
// straight out of it: no staging buffer, no conversion, and every chunk
// on its own thread (as many as --threads, which the runtime keeps in
// pool_size, so a 1-thread run stays a 1-thread run).

typedef struct {
  const uint8_t* src;   // memory to copy from, if any
  u32a*          dst;   // the block
  u64            n;     // bytes
  u64            slots; // slots in the block
  u64            off;   // file offset
  int            fd;
  int            err;
  uint8_t*       map;   // where to copy the bytes to, when writing via mmap
} ArrJob;

// A block for n packed bytes plus the count slot. Allocation stays on the
// calling thread (the allocator is per-lane); filling happens in parallel.
static Term arrays_alloc(Env e, u64 n, u32a** q, u64* slots) {
  u64 need = (n + 3) / 4 + 1;
  Cls c    = 1;
  while ((1ull << c) < need) {
    c += 1;
  }
  BLK_ALLOC(dst, c - 1)
  *q     = blk_ptr(e.mem, dst, 0);
  *slots = 1ull << c;
  return term_blk(false, c, dst);
}

// zero everything after the n data bytes, then store n in the last slot
static void arrays_seal(ArrJob* j) {
  uint8_t* b     = (uint8_t*)j->dst;
  u64      total = j->slots * 4;
  memset(b + j->n, 0, total - j->n);
  j->dst[j->slots - 1] = (u32)j->n;
}

static void arrays_pread(ArrJob* j) {
  uint8_t* b   = (uint8_t*)j->dst;
  u64      got = 0;
  while (got < j->n) {
    ssize_t r = pread(j->fd, b + got, j->n - got, (off_t)(j->off + got));
    if (r <= 0) {
      j->err = r < 0 ? errno : EIO;
      break;
    }
    got += (u64)r;
  }
  j->n = got;
  arrays_seal(j);
}

static void arrays_copy(ArrJob* j) {
  memcpy((uint8_t*)j->dst, j->src, j->n);
  arrays_seal(j);
}

typedef struct {
  ArrJob* jobs;
  u64     count;
  u64     stride;
  u64     first;
  void    (*fn)(ArrJob*);
} ArrLane;

static void* arrays_lane(void* p) {
  ArrLane* l = p;
  for (u64 i = l->first; i < l->count; i += l->stride) {
    l->fn(&l->jobs[i]);
  }
  return NULL;
}

static void arrays_par(ArrJob* jobs, u64 count, void (*fn)(ArrJob*)) {
  u64 t = pool_size < 1 ? 1 : (u64)pool_size;
  if (t > count) {
    t = count;
  }
  if (t <= 1) {
    for (u64 i = 0; i < count; i += 1) {
      fn(&jobs[i]);
    }
    return;
  }
  pthread_t* th = io_mem(malloc(t * sizeof(pthread_t)));
  ArrLane*   ls = io_mem(malloc(t * sizeof(ArrLane)));
  for (u64 i = 0; i < t; i += 1) {
    ls[i] = (ArrLane){ jobs, count, t, i, fn };
    pthread_create(&th[i], NULL, arrays_lane, &ls[i]);
  }
  for (u64 i = 0; i < t; i += 1) {
    pthread_join(th[i], NULL);
  }
  free(th);
  free(ls);
}

// Allocates a block per job, runs fn over them in parallel, and returns
// the blocks as a List, in order. Sets *err to the first failure.
static Term arrays_build(Env e, ArrJob* jobs, u64 k, void (*fn)(ArrJob*),
  u32* err) {
  Term* ts = io_mem(malloc((k ? k : 1) * sizeof(Term)));
  for (u64 i = 0; i < k; i += 1) {
    ts[i] = arrays_alloc(e, jobs[i].n, &jobs[i].dst, &jobs[i].slots);
  }
  arrays_par(jobs, k, fn);
  Term xs = term_pak(CID_NIL, 0);
  for (u64 i = k; i > 0; i -= 1) {
    if (jobs[i - 1].err && !*err) {
      *err = (u32)jobs[i - 1].err;
    }
    xs = io_node(e, CID_CON, ts[i - 1], xs, IO_HOTS & 16);
  }
  free(ts);
  return xs;
}

static void arrays_nothing(IoWork* w) {
}

#endif

// read_records(file, max, skip, rhdr): a file made of a `skip`-byte
// header and then records, each `rhdr` bytes of header whose first four
// hold the payload length (big-endian), followed by the payload. The
// result is the header, then one block per record. The file is read
// once; the records are copied into their blocks in parallel.
static void read_records_call(IoWork* w) {
  int     fd  = (int)w->hand;
  u64     got = 0;
  ssize_t n   = 1;
  while (n > 0 && got < w->word) {
    n = read(fd, w->data + got, w->word - got);
    if (n > 0) {
      got += (u64)n;
    }
  }
  w->size = io_sys_end(w, n < 0 ? n : (ssize_t)got);
}

static Term read_records_pack(Env e, IoWork* w) {
  Term xs  = term_pak(CID_NIL, 0);
  u32  err = w->code;
  if (!err) {
    const uint8_t* p    = (uint8_t*)w->data;
    u64            n    = w->size;
    u64            skip = (u64)w->made >> 32;
    u64            rhdr = (u64)w->made & 0xFFFFFFFF;
    u64            cap  = 16, cnt = 1;
    ArrJob*        jobs = io_mem(calloc(cap, sizeof(ArrJob)));
    jobs[0] = (ArrJob){ p, NULL, skip < n ? skip : n, 0, 0, -1, 0, NULL };
    for (u64 o = skip; rhdr >= 4 && o + rhdr <= n;) {
      u64 len = rhdr + ((u64)p[o] << 24 | (u64)p[o + 1] << 16
        | (u64)p[o + 2] << 8 | p[o + 3]);
      if (o + len > n) {
        len = n - o;
      }
      if (cnt == cap) {
        cap *= 2;
        jobs = io_mem(realloc(jobs, cap * sizeof(ArrJob)));
      }
      jobs[cnt] = (ArrJob){ p + o, NULL, len, 0, 0, -1, 0, NULL };
      cnt += 1;
      o   += len;
    }
    xs = arrays_build(e, jobs, cnt, arrays_copy, &err);
    free(jobs);
  }
  free(w->data);
  Term r = err ? io_fail(e, err, NULL) : io_done(e, xs);
  return io_tup(e, io_hand(w->hand), r);
}

Term read_records_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->word = f[1] < INT32_MAX ? (u32)f[1] : INT32_MAX;
  w->made = (intptr_t)(((u64)(u32)f[2] << 32) | (u32)f[3]);
  w->data = io_mem(malloc((u64)w->word + 1));
  return io_work(w, read_records_call, read_records_pack);
}

static void __attribute__((constructor)) read_records_use(void) {
  io_eff(CID_READ_RECORDS, read_records_run, 0);
}
