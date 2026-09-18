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

// write_arrays(file, xs): each block's n bytes (n in its last slot),
// concatenated. Offsets are summed up front, then every block is
// pwritten from where it lies, in parallel; the blocks are freed after.
static void arrays_pwrite(ArrJob* j) {
  const uint8_t* b   = (const uint8_t*)j->dst;
  u64            put = 0;
  while (put < j->n) {
    ssize_t r = pwrite(j->fd, b + put, j->n - put, (off_t)(j->off + put));
    if (r <= 0) {
      j->err = r < 0 ? errno : EIO;
      break;
    }
    put += (u64)r;
  }
}

static void arrays_mapcopy(ArrJob* j) {
  memcpy(j->map + j->off, (const uint8_t*)j->dst, j->n);
}

// Writing one file from many threads with pwrite serialises on the
// file's inode lock, so the fast route sizes the file, maps it shared and
// has every thread memcpy its chunks into place. The descriptor Bend
// opened is write-only; /proc/self/fd reopens the same file read-write,
// which mmap needs. Anything unusual (a pipe, no /proc) falls back to
// parallel pwrite.
static bool arrays_mapwrite(IoWork* w, ArrJob* jobs, u64 k) {
  u64 total = 0;
  for (u64 i = 0; i < k; i += 1) {
    total = jobs[i].off + jobs[i].n > total ? jobs[i].off + jobs[i].n : total;
  }
  if (total == 0) {
    return true;
  }
  char path[64];
  snprintf(path, sizeof path, "/proc/self/fd/%d", (int)w->hand);
  int fd = open(path, O_RDWR);
  if (fd < 0) {
    return false;
  }
  bool ok = ftruncate(fd, (off_t)total) == 0;
  uint8_t* p = ok ? mmap(NULL, total, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0)
    : MAP_FAILED;
  if (p == MAP_FAILED) {
    close(fd);
    return false;
  }
  for (u64 i = 0; i < k; i += 1) {
    jobs[i].map = p;
  }
  arrays_par(jobs, k, arrays_mapcopy);
  munmap(p, total);
  close(fd);
  return true;
}

static void write_arrays_call(IoWork* w) {
  ArrJob* jobs = (ArrJob*)w->data;
  if (!arrays_mapwrite(w, jobs, w->size)) {
    arrays_par(jobs, w->size, arrays_pwrite);
  }
  u32 err = 0;
  for (u64 i = 0; i < w->size && !err; i += 1) {
    err = (u32)jobs[i].err;
  }
  w->code = err;
}

static Term write_arrays_pack(Env e, IoWork* w) {
  ArrJob* jobs = (ArrJob*)w->data;
  Term*   ts   = (Term*)w->text;
  for (u64 i = 0; i < w->size; i += 1) {
    blk_free(e, ts[i]);
  }
  free(jobs);
  free(ts);
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, term_pak(CID_UNIT, 0));
  return io_tup(e, io_hand(w->hand), r);
}

Term write_arrays_run(Env e, Term* f, IoWork* w) {
  w->hand   = (intptr_t)io_hand_v(f[0]);
  int     fd   = (int)w->hand;
  u64     cap  = 64, k = 0, off = 0;
  ArrJob* jobs = io_mem(malloc(cap * sizeof(ArrJob)));
  Term*   ts   = io_mem(malloc(cap * sizeof(Term)));
  Term    xs   = f[1];
  while (term_aux(xs) == CID_CON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, xs, 2, fb));
    if (k == cap) {
      cap  *= 2;
      jobs  = io_mem(realloc(jobs, cap * sizeof(ArrJob)));
      ts    = io_mem(realloc(ts, cap * sizeof(Term)));
    }
    Term  a     = fb[0];
    u64   slots = 1ull << blk_cls(a);
    u32a* q     = blk_ptr(e.mem, term_loc(a), 0);
    u64   len   = q[slots - 1];
    if (len > (slots - 1) * 4) {
      len = (slots - 1) * 4;
    }
    jobs[k] = (ArrJob){ NULL, q, len, slots, off, fd, 0, NULL };
    ts[k]   = a;
    off    += len;
    k      += 1;
    xs      = fb[1];
  }
  w->data = (char*)jobs;
  w->text = (char*)ts;
  w->size = k;
  return io_work(w, write_arrays_call, write_arrays_pack);
}

static void __attribute__((constructor)) write_arrays_use(void) {
  io_eff(CID_WRITE_ARRAYS, write_arrays_run, 0);
}
