// The common block below is repeated in read_arrays.c, read_blob_arrays.c
// and write_arrays.c under one guard, so each effect also compiles alone.
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

// read_arrays(file, max, k): the file's first `max` bytes as k near-equal
// chunks, each pread straight into its block.
static Term read_arrays_pack(Env e, IoWork* w) {
  int         fd = (int)w->hand;
  struct stat st;
  u64         n  = w->word;
  if (fstat(fd, &st) == 0 && (u64)st.st_size < n) {
    n = (u64)st.st_size;
  }
  u64     k    = w->made > 0 ? (u64)w->made : 1;
  ArrJob* jobs = io_mem(calloc(k, sizeof(ArrJob)));
  for (u64 i = 0; i < k; i += 1) {
    jobs[i].off = i * n / k;
    jobs[i].n   = (i + 1) * n / k - jobs[i].off;
    jobs[i].fd  = fd;
  }
  u32  err = 0;
  Term xs  = arrays_build(e, jobs, k, arrays_pread, &err);
  free(jobs);
  Term r = err ? io_fail(e, err, NULL) : io_done(e, xs);
  return io_tup(e, io_hand(w->hand), r);
}

Term read_arrays_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->word = f[1] < INT32_MAX ? (u32)f[1] : INT32_MAX;
  w->made = (intptr_t)f[2];
  return io_work(w, arrays_nothing, read_arrays_pack);
}

static void __attribute__((constructor)) read_arrays_use(void) {
  io_eff(CID_READ_ARRAYS, read_arrays_run, 0);
}
