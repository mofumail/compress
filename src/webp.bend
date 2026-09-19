import Base
import ./fast.bend as F
import ./inflate.bend as I
import ./png.bend as P

# ======================================================================
# Lossless WebP (VP8L) decoding, following RFC 9649.
#
# Bits are read least-significant first, as in deflate, so the bit reader
# and the canonical-code builder of inflate.bend are reused, with table
# regions placed by offset. Pixels are ARGB words, one per slot.
#
# Table array `h`:
#   [416, 448)      scratch used by I.build
#   [512, 2900)     code lengths being read
#   [3072, 3091)    code-length code: lengths
#   [4096, 8192)    code-length code (a code block, see below)
#   8192 + (5 g + k) * 4096   code k of group g
# A code block: 10-bit table [0, 1024), count [1024, 1040), sorted
# symbols [1040, 3440), and at 3440: 1 + the symbol when the code has a
# single symbol (read with zero bits), else 0. (A 12-bit table was
# measured slower: more to build per group, and codes past 10 bits are
# rare enough.)
# ======================================================================

def A() -> Type:
  Array<U32>

def LENS() -> U32:
  512

def CLL() -> U32:
  3072

def CLB() -> U32:
  4096

def GB() -> U32:
  8192

def CSZ() -> U32:
  4096

def FLAG() -> U32:
  3440

def PB() -> U32:
  10

def CNT() -> U32:
  1024

def SYM() -> U32:
  1040

def base(+g: U32, +k: U32) -> U32:
  (GB() + (((g * 5 : U32) + k : U32) * CSZ() : U32) : U32)

# ------------------------------------------------ building a code

type NZ is Type:
  NZ{h: Array<U32>, i: U32, count: U32, last: U32}

def nz.b(+i: U32, +count: U32, +last: U32, pr: A() & U32) -> NZ:
  (h, +l) = pr
  +on = U32.is_ne(l, 0)
  NZ{h, (i + 1 : U32), Bool.pick(U32, on, (count + 1 : U32), count),
    Bool.pick(U32, on, i, last)}

def nz.loop(f: Nat, +lens: U32, s: NZ) -> NZ:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case NZ{h, +i, +count, +last}:
          nz.loop(g, lens, nz.b(i, count, last, F.get(h, (lens + i : U32))))

def mk.sel(single: Bool, h: A(), +lens: U32, +n: U32, +b: U32, +last: U32) -> A():
  match single:
    case True{}:
      Array.set(U32, h, (b + FLAG() : U32), (last + 1 : U32))
    case False{}:
      Array.set(U32, I.build_w(h, PB(), lens, n, (b + CNT() : U32), (b + SYM() : U32), b),
        (b + FLAG() : U32), 0)

def mk.b(+lens: U32, +n: U32, +b: U32, s: NZ) -> A():
  match s:
    case NZ{h, i, +count, +last}:
      mk.sel(U32.is_le(count, 1), h, lens, n, b, last)

# the code whose n lengths are at h[lens..], as a code block at b; a code
# with at most one used symbol reads no bits
def make(h: A(), +lens: U32, +n: U32, +b: U32) -> A():
  mk.b(lens, n, b, nz.loop(U32.to_nat(n), lens, NZ{h, 0, 0, 0}))

# one symbol of the code block at b
def ds.sel(single: Bool, h: A(), inp: A(), +pos: U32, +b: U32, +flag: U32) -> I.DY:
  match single:
    case True{}:
      I.DY{h, inp, pos, (flag - 1 : U32)}
    case False{}:
      I.decode_w(h, inp, pos, PB(), (b + CNT() : U32), (b + SYM() : U32), b)

def ds.b(inp: A(), +pos: U32, +b: U32, pr: A() & U32) -> I.DY:
  (h, +flag) = pr
  ds.sel(U32.is_ne(flag, 0), h, inp, pos, b, flag)

def dsym(h: A(), inp: A(), +pos: U32, +b: U32) -> I.DY:
  ds.b(inp, pos, b, F.get(h, (b + FLAG() : U32)))

# ------------------------------------------------ reading a code

type RC is Type:
  RC{inp: Array<U32>, h: Array<U32>, pos: U32}

def CLORDER() -> List<&2, U32>:
  [17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def cl3.b(+o: U32, h: A(), b: I.BR) -> RC:
  match b:
    case I.BR{inp, +pos, +v}:
      RC{inp, Array.set(U32, h, (CLL() + o : U32), v), pos}

def cl3.step(+o: U32, s: RC) -> RC:
  match s:
    case RC{inp, h, +pos}:
      cl3.b(o, h, I.bits(inp, pos, 3))

def cl3(f: Nat, xs: List<&2, U32>, s: RC) -> RC:
  match f:
    case 0n:
      s
    case 1n+g:
      match xs:
        case Nil{}:
          s
        case Con{+o, r}:
          cl3(g, r, cl3.step(o, s))

# The code lengths of a normal code. As in deflate, a plain length is
# "repeat once, no extra bits"; 16 repeats the last nonzero length (8 at
# first), 17 and 18 write zeros. `left` counts the code-length symbols
# the stream still allows.
type CL is Type:
  CL{inp: Array<U32>, h: Array<U32>, pos: U32, i: U32, prev: U32, left: U32,
    go: Bool}

def cl.c(h: A(), +n: U32, +i: U32, +prev: U32, +left: U32, +base: U32,
  +val: U32, b: I.BR) -> CL:
  match b:
    case I.BR{inp, +pos, +v}:
      +r = U32.min((base + v : U32), (n - i : U32))
      +i1 = (i + r : U32)
      +l1 = (left - 1 : U32)
      CL{inp, I.fill(U32.to_nat(r), (LENS() + i : U32), val, h), pos, i1, prev, l1,
        Bool.and(F.lt(i1, n), F.lt(0, l1))}

def cl.b(+n: U32, +i: U32, +prev: U32, +left: U32, d: I.DY) -> CL:
  match d:
    case I.DY{h, inp, +pos, +sym}:
      +small = F.lt(sym, 16)
      +w = Bool.pick(U32, small, 0, Bool.pick(U32, U32.is_eq(sym, 16), 2,
        Bool.pick(U32, U32.is_eq(sym, 17), 3, 7)))
      +base = Bool.pick(U32, small, 1, Bool.pick(U32, U32.is_eq(sym, 18), 11, 3))
      +val = Bool.pick(U32, small, sym, Bool.pick(U32, U32.is_eq(sym, 16), prev, 0))
      +prev1 = Bool.pick(U32, Bool.and(small, U32.is_ne(sym, 0)), sym, prev)
      cl.c(h, n, i, prev1, left, base, val, I.bits(inp, pos, w))

def cl.loop(f: Nat, +n: U32, s: CL) -> CL:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CL{inp, h, +pos, +i, +prev, +left, go}:
          match go:
            case False{}:
              CL{inp, h, pos, i, prev, left, False{}}
            case True{}:
              cl.loop(g, n, cl.b(n, i, prev, left, dsym(h, inp, pos, CLB())))

def rn.e(+n: U32, +b: U32, s: CL) -> RC:
  match s:
    case CL{inp, h, +pos, i, prev, left, go}:
      RC{inp, make(h, LENS(), n, b), pos}

def rn.d(+n: U32, +b: U32, +mx: U32, inp: A(), h: A(), +pos: U32) -> RC:
  rn.e(n, b, cl.loop(U32.to_nat((n + 1 : U32)), n, CL{inp,
    I.fill(U32.to_nat(n), LENS(), 0, h), pos, 0, 8, mx,
    Bool.and(F.lt(0, n), F.lt(0, mx))}))

def rn.c(h: A(), +n: U32, +b: U32, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +v}:
      rn.d(n, b, (2 + v : U32), inp, h, pos)

def rn.lim.b(h: A(), +n: U32, +b: U32, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +v}:
      rn.c(h, n, b, I.bits(inp, pos, (2 + (v << 1n : U32) : U32)))

def rn.lim(lim: Bool, inp: A(), h: A(), +pos: U32, +n: U32, +b: U32) -> RC:
  match lim:
    case False{}:
      rn.d(n, b, n, inp, h, pos)
    case True{}:
      rn.lim.b(h, n, b, I.bits(inp, pos, 3))

def rn.b(h: A(), +n: U32, +b: U32, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +v}:
      rn.lim(U32.is_eq(v, 1), inp, h, pos, n, b)

def rn.a(+n: U32, +b: U32, s: RC) -> RC:
  match s:
    case RC{inp, h, +pos}:
      rn.b(make(h, CLL(), 19, CLB()), n, b, I.bits(inp, pos, 1))

def normal.b(h: A(), +n: U32, +b: U32, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +v}:
      rn.a(n, b, cl3(U32.to_nat((v + 4 : U32)), CLORDER(),
        RC{inp, I.fill(19n, CLL(), 0, h), pos}))

def normal(inp: A(), h: A(), +pos: U32, +n: U32, +b: U32) -> RC:
  normal.b(h, n, b, I.bits(inp, pos, 4))

# A simple code: one or two symbols, each of length 1 (or 0 when alone).
def sm.fin(h: A(), inp: A(), +pos: U32, +n: U32, +b: U32, +s0: U32, +s1: U32,
  +two: Bool) -> RC:
  RC{inp, make(Array.set(U32, Array.set(U32, I.fill(U32.to_nat(n), LENS(), 0, h),
    (LENS() + s0 : U32), 1), (LENS() + Bool.pick(U32, two, s1, s0) : U32), 1),
    LENS(), n, b), pos}

def sm.c(h: A(), +n: U32, +b: U32, +s0: U32, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +s1}:
      sm.fin(h, inp, pos, n, b, s0, s1, True{})

def sm.two(two: Bool, h: A(), inp: A(), +pos: U32, +n: U32, +b: U32, +s0: U32) -> RC:
  match two:
    case False{}:
      sm.fin(h, inp, pos, n, b, s0, s0, False{})
    case True{}:
      sm.c(h, n, b, s0, I.bits(inp, pos, 8))

def sm.b(h: A(), +n: U32, +b: U32, +two: Bool, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +s0}:
      sm.two(two, h, inp, pos, n, b, s0)

def sm.a(h: A(), +n: U32, +b: U32, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +v}:
      +two = U32.is_eq((v .&. 1 : U32), 1)
      +w = Bool.pick(U32, U32.is_eq((v >> 1n : U32), 1), 8, 1)
      sm.b(h, n, b, two, I.bits(inp, pos, w))

def rd.sel(simple: Bool, inp: A(), h: A(), +pos: U32, +n: U32, +b: U32) -> RC:
  match simple:
    case True{}:
      sm.a(h, n, b, I.bits(inp, pos, 2))
    case False{}:
      normal(inp, h, pos, n, b)

def rd.a(h: A(), +n: U32, +b: U32, br: I.BR) -> RC:
  match br:
    case I.BR{inp, +pos, +v}:
      rd.sel(U32.is_eq(v, 1), inp, h, pos, n, b)

# Read a prefix code over an alphabet of n symbols into the block at b.
def read_code(inp: A(), h: A(), +pos: U32, +n: U32, +b: U32) -> RC:
  rd.a(h, n, b, I.bits(inp, pos, 1))

# ------------------------------------------------ the codes of every group
# Each group has five codes: green + length prefixes + colour-cache
# indices, red, blue, alpha, distance prefixes.

def gr.k4(+g: U32, s: RC) -> RC:
  match s:
    case RC{inp, h, +pos}:
      read_code(inp, h, pos, 40, base(g, 4))

def gr.k3(+g: U32, s: RC) -> RC:
  match s:
    case RC{inp, h, +pos}:
      gr.k4(g, read_code(inp, h, pos, 256, base(g, 3)))

def gr.k2(+g: U32, s: RC) -> RC:
  match s:
    case RC{inp, h, +pos}:
      gr.k3(g, read_code(inp, h, pos, 256, base(g, 2)))

def gr.k1(+g: U32, +cache: U32, s: RC) -> RC:
  match s:
    case RC{inp, h, +pos}:
      gr.k2(g, read_code(inp, h, pos, 256, base(g, 1)))

def gr.step(+g: U32, +cache: U32, s: RC) -> RC:
  match s:
    case RC{inp, h, +pos}:
      gr.k1(g, cache, read_code(inp, h, pos, (280 + cache : U32), base(g, 0)))

def groups(f: Nat, +g: U32, +cache: U32, s: RC) -> RC:
  match f:
    case 0n:
      s
    case 1n+k:
      groups(k, (g + 1 : U32), cache, gr.step(g, cache, s))

# ------------------------------------------------ lengths and distances

# a length or distance from its prefix symbol and extra bits
def pv.b(+off: U32, b: I.BR) -> I.BR:
  match b:
    case I.BR{inp, +pos, +v}:
      I.BR{inp, pos, (off + v + 1 : U32)}

def pv.sel(small: Bool, inp: A(), +pos: U32, +p: U32) -> I.BR:
  match small:
    case True{}:
      I.BR{inp, pos, (p + 1 : U32)}
    case False{}:
      +eb = ((p - 2 : U32) >> 1n : U32)
      pv.b(F.shl((2 + (p .&. 1 : U32) : U32), eb), I.bits(inp, pos, eb))

def prefix_value(inp: A(), +pos: U32, +p: U32) -> I.BR:
  pv.sel(F.lt(p, 4), inp, pos, p)

# The 120 short distance codes, as (dx, dy): a distance of dx + dy * width.
def DMAP() -> List<&2, U32>:
  [0, 1, 1, 0, 1, 1, 4294967295, 1, 0, 2, 2, 0, 1, 2, 4294967295, 2, 2, 1,
   4294967294, 1, 2, 2, 4294967294, 2, 0, 3, 3, 0, 1, 3, 4294967295, 3, 3, 1,
   4294967293, 1, 2, 3, 4294967294, 3, 3, 2, 4294967293, 2, 0, 4, 4, 0, 1, 4,
   4294967295, 4, 4, 1, 4294967292, 1, 3, 3, 4294967293, 3, 2, 4, 4294967294, 4,
   4, 2, 4294967292, 2, 0, 5, 3, 4, 4294967293, 4, 4, 3, 4294967292, 3, 5, 0,
   1, 5, 4294967295, 5, 5, 1, 4294967291, 1, 2, 5, 4294967294, 5, 5, 2,
   4294967291, 2, 4, 4, 4294967292, 4, 3, 5, 4294967293, 5, 5, 3, 4294967291, 3,
   0, 6, 6, 0, 1, 6, 4294967295, 6, 6, 1, 4294967290, 1, 2, 6, 4294967294, 6,
   6, 2, 4294967290, 2, 4, 5, 4294967292, 5, 5, 4, 4294967291, 4, 3, 6,
   4294967293, 6, 6, 3, 4294967290, 3, 0, 7, 7, 0, 1, 7, 4294967295, 7, 5, 5,
   4294967291, 5, 7, 1, 4294967289, 1, 4, 6, 4294967292, 6, 6, 4, 4294967290, 4,
   2, 7, 4294967294, 7, 7, 2, 4294967289, 2, 3, 7, 4294967293, 7, 7, 3,
   4294967289, 3, 5, 6, 4294967291, 6, 6, 5, 4294967290, 5, 8, 0, 4, 7,
   4294967292, 7, 7, 4, 4294967289, 4, 8, 1, 8, 2, 6, 6, 4294967290, 6, 8, 3,
   5, 7, 4294967291, 7, 7, 5, 4294967289, 5, 8, 4, 6, 7, 4294967290, 7, 7, 6,
   4294967289, 6, 8, 5, 7, 7, 4294967289, 7, 8, 6, 8, 7]

def dmap_at(+k: U32) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, DMAP(), U32.to_nat(k)), 0)

# the pixel distance for distance code c in an image `xs` pixels wide
def distance(+c: U32, +xs: U32) -> U32:
  +k = ((c - 1 : U32) << 1n : U32)
  +d = (dmap_at(k) + (dmap_at((k + 1 : U32)) * xs : U32) : U32)
  Bool.pick(U32, F.lt(120, c), (c - 120 : U32),
    Bool.pick(U32, Bool.or(U32.is_eq(d, 0), U32.is_le(2147483648, d)), 1, d))

# ------------------------------------------------ pixels
# Every decoded pixel, whatever produced it, also goes into the colour
# cache (a 2^cb-slot hash of recent colours), as in libwebp.

type PX is Type:
  PX{inp: Array<U32>, h: Array<U32>, out: Array<U32>, cache: Array<U32>,
    meta: Array<U32>, pos: U32, i: U32, go: Bool}

def argb(+a: U32, +r: U32, +g: U32, +b: U32) -> U32:
  ((a << 24n : U32) .|. (r << 16n : U32) .|. (g << 8n : U32) .|. b : U32)

def ckey(+col: U32, +cb: U32) -> U32:
  Bool.pick(U32, U32.is_eq(cb, 0), 0,
    F.shr((col * 506832829 : U32), ((32 - cb : U32) .&. 31 : U32)))

# out[i] := col, and col into the cache
def emit(out: A(), cache: A(), +i: U32, +col: U32, +cb: U32) -> A() & A():
  (Array.set(U32, out, i, col), Array.set(U32, cache, ckey(col, cb), col))

def px.put(inp: A(), h: A(), meta: A(), +pos: U32, +i: U32, +n: U32,
  +k: U32, oc: A() & A()) -> PX:
  (out, cache) = oc
  +i1 = (i + k : U32)
  PX{inp, h, out, cache, meta, pos, i1, F.lt(i1, n)}

# a run copied from `dist` pixels back
type CP is Type:
  CP{out: Array<U32>, cache: Array<U32>, i: U32}

def cp.c(+i: U32, oc: A() & A()) -> CP:
  (out, cache) = oc
  CP{out, cache, (i + 1 : U32)}

def cp.b(cache: A(), +i: U32, +cb: U32, pr: A() & U32) -> CP:
  (out, +v) = pr
  cp.c(i, emit(out, cache, i, v, cb))

def cp.loop(f: Nat, +dist: U32, +cb: U32, s: CP) -> CP:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CP{out, cache, +i}:
          cp.loop(g, dist, cb, cp.b(cache, i, cb, F.get(out, (i - dist : U32))))

def px.copied(inp: A(), h: A(), meta: A(), +pos: U32, +n: U32, c: CP) -> PX:
  match c:
    case CP{out, cache, +i}:
      PX{inp, h, out, cache, meta, pos, i, F.lt(i, n)}

def px.dist(out: A(), cache: A(), meta: A(), h: A(), +i: U32, +n: U32, +xs: U32,
  +cb: U32, +len: U32, b: I.BR) -> PX:
  match b:
    case I.BR{inp, +pos, +dc}:
      +span = U32.min(len, (n - i : U32))
      px.copied(inp, h, meta, pos, n,
        cp.loop(U32.to_nat(span), distance(dc, xs), cb, CP{out, cache, i}))

def px.dsym(out: A(), cache: A(), meta: A(), +i: U32, +n: U32, +xs: U32,
  +cb: U32, +len: U32, d: I.DY) -> PX:
  match d:
    case I.DY{h, inp, +pos, +p}:
      px.dist(out, cache, meta, h, i, n, xs, cb, len, prefix_value(inp, pos, p))

def px.len(out: A(), cache: A(), meta: A(), h: A(), +i: U32, +n: U32,
  +xs: U32, +cb: U32, +g: U32, b: I.BR) -> PX:
  match b:
    case I.BR{inp, +pos, +len}:
      px.dsym(out, cache, meta, i, n, xs, cb, len, dsym(h, inp, pos, base(g, 4)))

def px.a3(out: A(), cache: A(), meta: A(), +i: U32, +n: U32, +cb: U32,
  +green: U32, +red: U32, +blue: U32, d: I.DY) -> PX:
  match d:
    case I.DY{h, inp, +pos, +alpha}:
      px.put(inp, h, meta, pos, i, n, 1, emit(out, cache, i,
        ((alpha << 24n : U32) .|. (red << 16n : U32) .|. (green << 8n : U32) .|. blue : U32),
        cb))

def px.a2(out: A(), cache: A(), meta: A(), +i: U32, +n: U32, +cb: U32,
  +g: U32, +green: U32, +red: U32, d: I.DY) -> PX:
  match d:
    case I.DY{h, inp, +pos, +blue}:
      px.a3(out, cache, meta, i, n, cb, green, red, blue, dsym(h, inp, pos, base(g, 3)))

def px.a1(out: A(), cache: A(), meta: A(), +i: U32, +n: U32, +cb: U32,
  +g: U32, +green: U32, d: I.DY) -> PX:
  match d:
    case I.DY{h, inp, +pos, +red}:
      px.a2(out, cache, meta, i, n, cb, g, green, red, dsym(h, inp, pos, base(g, 2)))

def px.cached(inp: A(), h: A(), out: A(), meta: A(), +pos: U32, +i: U32,
  +n: U32, +cb: U32, pr: A() & U32) -> PX:
  (cache, +col) = pr
  px.put(inp, h, meta, pos, i, n, 1, emit(out, cache, i, col, cb))

def px.kind(lit: Bool, backref: Bool, inp: A(), h: A(), out: A(), cache: A(),
  meta: A(), +pos: U32, +i: U32, +n: U32, +xs: U32, +cb: U32, +g: U32,
  +s: U32) -> PX:
  match lit:
    case True{}:
      px.a1(out, cache, meta, i, n, cb, g, s, dsym(h, inp, pos, base(g, 1)))
    case False{}:
      match backref:
        case True{}:
          px.len(out, cache, meta, h, i, n, xs, cb, g,
            prefix_value(inp, pos, (s - 256 : U32)))
        case False{}:
          px.cached(inp, h, out, meta, pos, i, n, cb, F.get(cache, (s - 280 : U32)))

def px.green(out: A(), cache: A(), meta: A(), +i: U32, +n: U32, +xs: U32,
  +cb: U32, +g: U32, d: I.DY) -> PX:
  match d:
    case I.DY{h, inp, +pos, +s}:
      px.kind(F.lt(s, 256), F.lt(s, 280), inp, h, out, cache, meta, pos, i, n,
        xs, cb, g, s)

def px.group(inp: A(), h: A(), out: A(), cache: A(), +pos: U32, +i: U32,
  +n: U32, +xs: U32, +cb: U32, +has: Bool, pr: A() & U32) -> PX:
  (meta, +m) = pr
  +g = Bool.pick(U32, has, ((m >> 8n : U32) .&. 65535 : U32), 0)
  px.green(out, cache, meta, i, n, xs, cb, g, dsym(h, inp, pos, base(g, 0)))

def px.loop(f: Nat, +n: U32, +xs: U32, +cb: U32, +mb: U32, +mw: U32,
  +has: Bool, s: PX) -> PX:
  match f:
    case 0n:
      s
    case 1n+k:
      match s:
        case PX{inp, h, out, cache, meta, +pos, +i, go}:
          match go:
            case False{}:
              PX{inp, h, out, cache, meta, pos, i, False{}}
            case True{}:
              +y = (i / xs : U32)
              +x = (i - (y * xs : U32) : U32)
              px.loop(k, n, xs, cb, mb, mw, has, px.group(inp, h, out, cache, pos, i,
                n, xs, cb, has, F.get(meta,
                  ((F.shr(y, mb) * mw : U32) + F.shr(x, mb) : U32))))

# ------------------------------------------------ entropy-coded images

type DI is Type:
  DI{inp: Array<U32>, pos: U32, px: Array<U32>}

def px.fin(s: PX) -> DI:
  match s:
    case PX{inp, h, out, cache, meta, +pos, i, go}:
      DI{inp, pos, out}

# the pixels, once the codes are read
def run(+n: U32, +xs: U32, +cb: U32, +mb: U32, +mw: U32, +has: Bool,
  meta: A(), s: RC) -> DI:
  match s:
    case RC{inp, h, +pos}:
      px.fin(px.loop(U32.to_nat(n), n, xs, cb, mb, mw, has, PX{inp, h,
        Array.new(U32, F.depth(32n, 1n, (n + 1 : U32)), 0),
        Array.new(U32, U32.to_nat(cb), 0), meta, pos, 0, F.lt(0, n)}))

def cache_size(+cb: U32) -> U32:
  Bool.pick(U32, U32.is_eq(cb, 0), 0, F.shl(1, cb))

def codes_array(+groups: U32) -> A():
  Array.new(U32, F.depth(32n, 1n, base(groups, 0)), 0)

# colour-cache bits: a flag, then 4 bits
def cc.b(b: I.BR) -> I.BR:
  match b:
    case I.BR{inp, +pos, +v}:
      I.BR{inp, pos, v}

def cc.sel(on: Bool, inp: A(), +pos: U32) -> I.BR:
  match on:
    case True{}:
      I.bits(inp, pos, 4)
    case False{}:
      I.BR{inp, pos, 0}

def cc.a(b: I.BR) -> I.BR:
  match b:
    case I.BR{inp, +pos, +v}:
      cc.sel(U32.is_eq(v, 1), inp, pos)

def cache_bits(inp: A(), +pos: U32) -> I.BR:
  cc.a(I.bits(inp, pos, 1))

# A sub-image (transform data, colour table, entropy image): one group.
def plain.b(+w: U32, +ht: U32, b: I.BR) -> DI:
  match b:
    case I.BR{inp, +pos, +cb}:
      run((w * ht : U32), w, cb, 0, 1, False{}, Array.new(U32, 1n, 0),
        groups(1n, 0, cache_size(cb), RC{inp, codes_array(1), pos}))

def decode_plain(inp: A(), +pos: U32, +w: U32, +ht: U32) -> DI:
  plain.b(w, ht, cache_bits(inp, pos))

# the number of groups: one more than the largest index in the entropy image
type MX is Type:
  MX{a: Array<U32>, i: U32, mx: U32}

def mx.b(+i: U32, +mx: U32, pr: A() & U32) -> MX:
  (a, +v) = pr
  MX{a, (i + 1 : U32), U32.max(mx, ((v >> 8n : U32) .&. 65535 : U32))}

def mx.loop(f: Nat, s: MX) -> MX:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case MX{a, +i, +mx}:
          mx.loop(g, mx.b(i, mx, F.get(a, i)))

def mx.fin(+n: U32, +xs: U32, +cb: U32, +mb: U32, +mw: U32, s: MX, inp: A(), +pos: U32) -> DI:
  match s:
    case MX{a, i, +mx}:
      +ng = (mx + 1 : U32)
      run(n, xs, cb, mb, mw, True{}, a,
        groups(U32.to_nat(ng), 0, cache_size(cb), RC{inp, codes_array(ng), pos}))

def mn.meta(+n: U32, +xs: U32, +cb: U32, +mb: U32, +mw: U32, +mh: U32, d: DI) -> DI:
  match d:
    case DI{inp, +pos, meta}:
      mx.fin(n, xs, cb, mb, mw, mx.loop(U32.to_nat((mw * mh : U32)), MX{meta, 0, 0}),
        inp, pos)

def mn.c(+w: U32, +ht: U32, +cb: U32, b: I.BR) -> DI:
  match b:
    case I.BR{inp, +pos, +v}:
      +mb = (v + 2 : U32)
      +mw = ((w + F.shl(1, mb) - 1 : U32) >> U32.to_nat(mb) : U32)
      +mh = ((ht + F.shl(1, mb) - 1 : U32) >> U32.to_nat(mb) : U32)
      mn.meta((w * ht : U32), w, cb, mb, mw, mh, decode_plain(inp, pos, mw, mh))

def mn.sel(meta: Bool, inp: A(), +pos: U32, +w: U32, +ht: U32, +cb: U32) -> DI:
  match meta:
    case True{}:
      mn.c(w, ht, cb, I.bits(inp, pos, 3))
    case False{}:
      run((w * ht : U32), w, cb, 0, 1, False{}, Array.new(U32, 1n, 0),
        groups(1n, 0, cache_size(cb), RC{inp, codes_array(1), pos}))

def mn.b(+w: U32, +ht: U32, +cb: U32, b: I.BR) -> DI:
  match b:
    case I.BR{inp, +pos, +v}:
      mn.sel(U32.is_eq(v, 1), inp, pos, w, ht, cb)

def mn.a(+w: U32, +ht: U32, b: I.BR) -> DI:
  match b:
    case I.BR{inp, +pos, +cb}:
      mn.b(w, ht, cb, I.bits(inp, pos, 1))

# The main image: may split into groups by an entropy image.
def decode_main(inp: A(), +pos: U32, +w: U32, +ht: U32) -> DI:
  mn.a(w, ht, cache_bits(inp, pos))

# ------------------------------------------------ per-channel arithmetic
# ARGB words; each channel a byte, modulo 256 unless clamped.

def chn(+p: U32, +k: U32) -> U32:
  (F.shr(p, (k << 3n : U32)) .&. 255 : U32)

def add4(+a: U32, +b: U32) -> U32:
  ((((a .&. 16711935 : U32) + (b .&. 16711935 : U32) : U32) .&. 16711935 : U32) .|.
   (((a .&. 4278255360 : U32) + (b .&. 4278255360 : U32) : U32) .&. 4278255360 : U32) : U32)

def avg2(+a: U32, +b: U32) -> U32:
  ((((a .^. b : U32) .&. 4278124286 : U32) >> 1n : U32) + (a .&. b : U32) : U32)

def adiff(+x: U32, +y: U32) -> U32:
  Bool.pick(U32, U32.is_le(y, x), (x - y : U32), (y - x : U32))

def sad(+a: U32, +b: U32) -> U32:
  (adiff(chn(a, 0), chn(b, 0)) + adiff(chn(a, 1), chn(b, 1)) +
   adiff(chn(a, 2), chn(b, 2)) + adiff(chn(a, 3), chn(b, 3)) : U32)

# L or T, whichever is nearer to the gradient L + T - TL
def select(+l: U32, +t: U32, +tl: U32) -> U32:
  Bool.pick(U32, F.lt(sad(t, tl), sad(l, tl)), l, t)

def cfull1(+a: U32, +b: U32, +c: U32) -> U32:
  +s = (a + b : U32)
  U32.min(255, Bool.pick(U32, U32.is_le(c, s), (s - c : U32), 0))

def cfull(+a: U32, +b: U32, +c: U32) -> U32:
  argb(cfull1(chn(a, 3), chn(b, 3), chn(c, 3)), cfull1(chn(a, 2), chn(b, 2), chn(c, 2)),
    cfull1(chn(a, 1), chn(b, 1), chn(c, 1)), cfull1(chn(a, 0), chn(b, 0), chn(c, 0)))

# a + (a - b) / 2, the division truncating toward zero, clamped
def chalf1(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_le(b, a), U32.min(255, (a + ((a - b : U32) >> 1n : U32) : U32)),
    Bool.pick(U32, U32.is_le(((b - a : U32) >> 1n : U32), a), (a - ((b - a : U32) >> 1n : U32) : U32), 0))

def chalf(+a: U32, +b: U32) -> U32:
  argb(chalf1(chn(a, 3), chn(b, 3)), chalf1(chn(a, 2), chn(b, 2)),
    chalf1(chn(a, 1), chn(b, 1)), chalf1(chn(a, 0), chn(b, 0)))

# the fourteen predictors (14 and 15 predict black, like 0)
def mode(m: Nat, +l: U32, +t: U32, +tl: U32, +tr: U32) -> U32:
  match m:
    case 0n:
      4278190080
    case 1n+m1:
      match m1:
        case 0n:
          l
        case 1n+m2:
          match m2:
            case 0n:
              t
            case 1n+m3:
              match m3:
                case 0n:
                  tr
                case 1n+m4:
                  match m4:
                    case 0n:
                      tl
                    case 1n+m5:
                      match m5:
                        case 0n:
                          avg2(avg2(l, tr), t)
                        case 1n+m6:
                          match m6:
                            case 0n:
                              avg2(l, tl)
                            case 1n+m7:
                              match m7:
                                case 0n:
                                  avg2(l, t)
                                case 1n+m8:
                                  match m8:
                                    case 0n:
                                      avg2(tl, t)
                                    case 1n+m9:
                                      match m9:
                                        case 0n:
                                          avg2(t, tr)
                                        case 1n+m10:
                                          match m10:
                                            case 0n:
                                              avg2(avg2(l, tl), avg2(t, tr))
                                            case 1n+m11:
                                              match m11:
                                                case 0n:
                                                  select(l, t, tl)
                                                case 1n+m12:
                                                  match m12:
                                                    case 0n:
                                                      cfull(l, t, tl)
                                                    case 1n+m13:
                                                      match m13:
                                                        case 0n:
                                                          chalf(avg2(l, t), tl)
                                                        case 1n+m14:
                                                          4278190080

# ------------------------------------------------ inverse predictor

type PR is Type:
  PR{px: Array<U32>, data: Array<U32>, i: U32, x: U32, y: U32}

def pr.f(data: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +r: U32, +pred: U32,
  px: A()) -> PR:
  +x1 = (x + 1 : U32)
  +wrap = U32.is_eq(x1, xs)
  PR{Array.set(U32, px, i, add4(r, pred)), data, (i + 1 : U32),
    Bool.pick(U32, wrap, 0, x1), Bool.pick(U32, wrap, (y + 1 : U32), y)}

def pr.e(px: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +r: U32, +l: U32,
  +t: U32, +tl: U32, +tr: U32, pr: A() & U32) -> PR:
  (data, +e) = pr
  +pred = Bool.pick(U32, U32.is_eq(i, 0), 4278190080,
    Bool.pick(U32, U32.is_eq(y, 0), l, Bool.pick(U32, U32.is_eq(x, 0), t,
      mode(U32.to_nat(((e >> 8n : U32) .&. 15 : U32)), l, t, tl, tr))))
  pr.f(data, i, x, y, xs, r, pred, px)

def pr.d(data: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +b: U32, +bw: U32,
  +r: U32, +l: U32, +t: U32, +tl: U32, pr: A() & U32) -> PR:
  (px, +tr) = pr
  pr.e(px, i, x, y, xs, r, l, t, tl, tr,
    F.get(data, ((F.shr(y, b) * bw : U32) + F.shr(x, b) : U32)))

def pr.c(data: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +b: U32, +bw: U32,
  +r: U32, +l: U32, +t: U32, pr: A() & U32) -> PR:
  (px, +tl) = pr
  pr.d(data, i, x, y, xs, b, bw, r, l, t, tl, F.get(px, ((i - xs : U32) + 1 : U32)))

def pr.b(data: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +b: U32, +bw: U32,
  +r: U32, +l: U32, pr: A() & U32) -> PR:
  (px, +t) = pr
  pr.c(data, i, x, y, xs, b, bw, r, l, t, F.get(px, ((i - xs : U32) - 1 : U32)))

def pr.a2(data: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +b: U32, +bw: U32,
  +r: U32, pr: A() & U32) -> PR:
  (px, +l) = pr
  pr.b(data, i, x, y, xs, b, bw, r, l, F.get(px, (i - xs : U32)))

def pr.a(data: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +b: U32, +bw: U32,
  pr: A() & U32) -> PR:
  (px, +r) = pr
  pr.a2(data, i, x, y, xs, b, bw, r, F.get(px, (i - 1 : U32)))

def pr.loop(f: Nat, +xs: U32, +b: U32, +bw: U32, s: PR) -> PR:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case PR{px, data, +i, +x, +y}:
          pr.loop(g, xs, b, bw, pr.a(data, i, x, y, xs, b, bw, F.get(px, i)))

def pr.fin(s: PR) -> A():
  match s:
    case PR{px, data, i, x, y}:
      px

def blocks(+n: U32, +b: U32) -> U32:
  ((n + F.shl(1, b) - 1 : U32) >> U32.to_nat(b) : U32)

def predictor(px: A(), data: A(), +xs: U32, +ys: U32, +b: U32) -> A():
  pr.fin(pr.loop(U32.to_nat((xs * ys : U32)), xs, b, blocks(xs, b),
    PR{px, data, 0, 0, 0}))

# ------------------------------------------------ inverse cross-colour

# (int8 t * int8 c) >> 5, arithmetic, as a U32 to add modulo 256
def delta(+t: U32, +c: U32) -> U32:
  +nt = U32.is_le(128, t)
  +nc = U32.is_le(128, c)
  +m = (Bool.pick(U32, nt, (256 - t : U32), t) * Bool.pick(U32, nc, (256 - c : U32), c) : U32)
  Bool.pick(U32, Bool.xor(nt, nc), (0 - ((m + 31 : U32) >> 5n : U32) : U32), (m >> 5n : U32))

def cross1(+p: U32, +e: U32) -> U32:
  +g = chn(p, 1)
  +nr = ((chn(p, 2) + delta((e .&. 255 : U32), g) : U32) .&. 255 : U32)
  +nb = ((chn(p, 0) + delta(chn(e, 1), g) + delta(chn(e, 2), nr) : U32) .&. 255 : U32)
  argb(chn(p, 3), nr, g, nb)

type XC is Type:
  XC{px: Array<U32>, data: Array<U32>, i: U32, x: U32, y: U32}

def xc.b(px: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +p: U32, pr: A() & U32) -> XC:
  (data, +e) = pr
  +x1 = (x + 1 : U32)
  +wrap = U32.is_eq(x1, xs)
  XC{Array.set(U32, px, i, cross1(p, e)), data, (i + 1 : U32),
    Bool.pick(U32, wrap, 0, x1), Bool.pick(U32, wrap, (y + 1 : U32), y)}

def xc.a(data: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +b: U32, +bw: U32,
  pr: A() & U32) -> XC:
  (px, +p) = pr
  xc.b(px, i, x, y, xs, p, F.get(data, ((F.shr(y, b) * bw : U32) + F.shr(x, b) : U32)))

def xc.loop(f: Nat, +xs: U32, +b: U32, +bw: U32, s: XC) -> XC:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case XC{px, data, +i, +x, +y}:
          xc.loop(g, xs, b, bw, xc.a(data, i, x, y, xs, b, bw, F.get(px, i)))

def xc.fin(s: XC) -> A():
  match s:
    case XC{px, data, i, x, y}:
      px

def cross(px: A(), data: A(), +xs: U32, +ys: U32, +b: U32) -> A():
  xc.fin(xc.loop(U32.to_nat((xs * ys : U32)), xs, b, blocks(xs, b),
    XC{px, data, 0, 0, 0}))

# ------------------------------------------------ inverse subtract-green

def sg.b(+i: U32, pr: A() & U32) -> A():
  (px, +p) = pr
  +g = chn(p, 1)
  Array.set(U32, px, i, ((p .&. 4278255360 : U32) .|.
    (((p .&. 16711935 : U32) + ((g << 16n : U32) .|. g : U32) : U32) .&. 16711935 : U32) : U32))

def sg.loop(f: Nat, +i: U32, px: A()) -> A():
  match f:
    case 0n:
      px
    case 1n+g:
      sg.loop(g, (i + 1 : U32), sg.b(i, F.get(px, i)))

# ------------------------------------------------ inverse colour indexing
# Indices were bundled 2, 4 or 8 to a pixel (in its green byte) when the
# table is small; each output pixel takes its bits and looks them up.

type CI is Type:
  CI{inp: Array<U32>, tab: Array<U32>, out: Array<U32>, i: U32, x: U32, y: U32}

def ci.c(inp: A(), out: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +size: U32,
  +ix: U32, pr: A() & U32) -> CI:
  (tab, +c) = pr
  +x1 = (x + 1 : U32)
  +wrap = U32.is_eq(x1, xs)
  CI{inp, tab, Array.set(U32, out, i, Bool.pick(U32, F.lt(ix, size), c, 0)),
    (i + 1 : U32), Bool.pick(U32, wrap, 0, x1), Bool.pick(U32, wrap, (y + 1 : U32), y)}

def ci.b(tab: A(), out: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +wb: U32,
  +size: U32, pr: A() & U32) -> CI:
  (inp, +p) = pr
  +bpp = F.shr(8, wb)
  +sh = ((x .&. (F.shl(1, wb) - 1 : U32) : U32) * bpp : U32)
  +ix = (F.shr(chn(p, 1), sh) .&. (F.shl(1, bpp) - 1 : U32) : U32)
  ci.c(inp, out, i, x, y, xs, size, ix, F.get(tab, (ix .&. 255 : U32)))

def ci.loop(f: Nat, +xs: U32, +pw: U32, +wb: U32, +size: U32, s: CI) -> CI:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CI{inp, tab, out, +i, +x, +y}:
          ci.loop(g, xs, pw, wb, size, ci.b(tab, out, i, x, y, xs, wb, size,
            F.get(inp, ((y * pw : U32) + F.shr(x, wb) : U32))))

def ci.fin(s: CI) -> A():
  match s:
    case CI{inp, tab, out, i, x, y}:
      out

def unindex(px: A(), tab: A(), +xs: U32, +ys: U32, +wb: U32, +size: U32) -> A():
  +n = (xs * ys : U32)
  ci.fin(ci.loop(U32.to_nat(n), xs, blocks(xs, wb), wb, size,
    CI{px, tab, Array.new(U32, F.depth(32n, 1n, (n + 1 : U32)), 0), 0, 0, 0}))

# the colour table is sent as differences from the previous entry
def dt.b(+i: U32, +prev: U32, pr: A() & U32) -> A():
  (t, +v) = pr
  Array.set(U32, t, i, add4(v, prev))

def dt.a(+i: U32, pr: A() & U32) -> A():
  (t, +prev) = pr
  dt.b(i, prev, F.get(t, i))

def dt.loop(f: Nat, +i: U32, t: A()) -> A():
  match f:
    case 0n:
      t
    case 1n+g:
      dt.loop(g, (i + 1 : U32), dt.a(i, F.get(t, (i - 1 : U32))))

# ------------------------------------------------ the transform list

type TR is Type:
  TR{kind: U32, b: U32, xs: U32, ys: U32, size: U32, data: Array<U32>}

type TL is Type:
  TL{inp: Array<U32>, pos: U32, xs: U32, ys: U32, trs: List<&1, TR>, go: Bool}

def tl.sub(+kind: U32, +b: U32, +xs: U32, +ys: U32, trs: List<&1, TR>, d: DI) -> TL:
  match d:
    case DI{inp, +pos, data}:
      TL{inp, pos, xs, ys, Con{TR{kind, b, xs, ys, 0, data}, trs}, True{}}

def tl.pb(+kind: U32, +xs: U32, +ys: U32, trs: List<&1, TR>, br: I.BR) -> TL:
  match br:
    case I.BR{inp, +pos, +v}:
      +b = (v + 2 : U32)
      tl.sub(kind, b, xs, ys, trs, decode_plain(inp, pos, blocks(xs, b), blocks(ys, b)))

def tl.tab(+xs: U32, +ys: U32, +size: U32, trs: List<&1, TR>, d: DI) -> TL:
  match d:
    case DI{inp, +pos, t}:
      +wb = Bool.pick(U32, U32.is_le(size, 2), 3, Bool.pick(U32, U32.is_le(size, 4), 2,
        Bool.pick(U32, U32.is_le(size, 16), 1, 0)))
      TL{inp, pos, blocks(xs, wb), ys,
        Con{TR{3, wb, xs, ys, size, dt.loop(U32.to_nat((size - 1 : U32)), 1, t)}, trs},
        True{}}

def tl.ci(+xs: U32, +ys: U32, trs: List<&1, TR>, br: I.BR) -> TL:
  match br:
    case I.BR{inp, +pos, +v}:
      +size = (v + 1 : U32)
      tl.tab(xs, ys, size, trs, decode_plain(inp, pos, size, 1))

def tl.kind(k0: Bool, k1: Bool, k2: Bool, inp: A(), +pos: U32, +xs: U32,
  +ys: U32, trs: List<&1, TR>) -> TL:
  match k0:
    case True{}:
      tl.pb(0, xs, ys, trs, I.bits(inp, pos, 3))
    case False{}:
      match k1:
        case True{}:
          tl.pb(1, xs, ys, trs, I.bits(inp, pos, 3))
        case False{}:
          match k2:
            case True{}:
              TL{inp, pos, xs, ys, Con{TR{2, 0, xs, ys, 0, Array.new(U32, 1n, 0)}, trs},
                True{}}
            case False{}:
              tl.ci(xs, ys, trs, I.bits(inp, pos, 8))

def tl.k(+xs: U32, +ys: U32, trs: List<&1, TR>, br: I.BR) -> TL:
  match br:
    case I.BR{inp, +pos, +k}:
      tl.kind(U32.is_eq(k, 0), U32.is_eq(k, 1), U32.is_eq(k, 2), inp, pos, xs, ys, trs)

def tl.sel(more: Bool, inp: A(), +pos: U32, +xs: U32, +ys: U32,
  trs: List<&1, TR>) -> TL:
  match more:
    case False{}:
      TL{inp, pos, xs, ys, trs, False{}}
    case True{}:
      tl.k(xs, ys, trs, I.bits(inp, pos, 2))

def tl.a(+xs: U32, +ys: U32, trs: List<&1, TR>, br: I.BR) -> TL:
  match br:
    case I.BR{inp, +pos, +v}:
      tl.sel(U32.is_eq(v, 1), inp, pos, xs, ys, trs)

def tl.loop(f: Nat, s: TL) -> TL:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case TL{inp, +pos, +xs, +ys, trs, go}:
          match go:
            case False{}:
              TL{inp, pos, xs, ys, trs, False{}}
            case True{}:
              tl.loop(g, tl.a(xs, ys, trs, I.bits(inp, pos, 1)))

# transforms undo in the reverse of the order they were read, which is
# the order of the list (it was built by prepending)
def undo1(kind: Nat, px: A(), data: A(), +b: U32, +xs: U32, +ys: U32, +size: U32) -> A():
  match kind:
    case 0n:
      predictor(px, data, xs, ys, b)
    case 1n+k1:
      match k1:
        case 0n:
          cross(px, data, xs, ys, b)
        case 1n+k2:
          match k2:
            case 0n:
              sg.loop(U32.to_nat((xs * ys : U32)), 0, px)
            case 1n+k3:
              unindex(px, data, xs, ys, b, size)

def undo.one(tr: TR, px: A()) -> A():
  match tr:
    case TR{+kind, +b, +xs, +ys, +size, data}:
      undo1(U32.to_nat(kind), px, data, b, xs, ys, size)

# ------------------------------------------------ to the image record

def undo(trs: List<&1, TR>, px: A()) -> A():
  match trs:
    case Nil{}:
      px
    case Con{tr, rest}:
      undo(rest, undo.one(tr, px))

type OU is Type:
  OU{px: Array<U32>, out: Array<U32>, i: U32}

def ou.b(out: A(), +i: U32, +ch: U32, pr: A() & U32) -> OU:
  (px, +p) = pr
  +rgb = (chn(p, 2) .|. (chn(p, 1) << 8n : U32) .|. (chn(p, 0) << 16n : U32) : U32)
  OU{px, P.putn(U32.to_nat(ch), (i * ch : U32), (rgb .|. (chn(p, 3) << 24n : U32) : U32), out),
    (i + 1 : U32)}

def ou.loop(f: Nat, +ch: U32, s: OU) -> OU:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case OU{px, out, +i}:
          ou.loop(g, ch, ou.b(out, i, ch, F.get(px, i)))

def ou.fin(+len: U32, s: OU) -> A():
  match s:
    case OU{px, out, i}:
      F.pack_cap(out, len)

def to_image(px: A(), +w: U32, +h: U32, +ch: U32, +ok: Bool) -> P.IM:
  +n = (w * h : U32)
  +len = (n * ch : U32)
  P.IM{ou.fin(len, ou.loop(U32.to_nat(n), ch, OU{px, F.new_packed(len), 0})),
    w, h, ch, 1, ok, Nil{}, 0}

# ------------------------------------------------ the VP8L bitstream

type IX is Type:
  IX{inp: Array<U32>, out: Array<U32>, i: U32, x: U32, y: U32}

def ix.b(out: A(), +i: U32, +x: U32, +y: U32, +xs: U32, +wb: U32, pr: A() & U32) -> IX:
  (inp, +p) = pr
  +bpp = F.shr(8, wb)
  +sh = ((x .&. (F.shl(1, wb) - 1 : U32) : U32) * bpp : U32)
  +x1 = (x + 1 : U32)
  +wrap = U32.is_eq(x1, xs)
  IX{inp, F.set_byte(out, i, (F.shr(chn(p, 1), sh) .&. (F.shl(1, bpp) - 1 : U32) : U32)),
    (i + 1 : U32), Bool.pick(U32, wrap, 0, x1), Bool.pick(U32, wrap, (y + 1 : U32), y)}

def ix.loop(f: Nat, +xs: U32, +pw: U32, +wb: U32, s: IX) -> IX:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case IX{inp, out, +i, +x, +y}:
          ix.loop(g, xs, pw, wb, ix.b(out, i, x, y, xs, wb,
            F.get(inp, ((y * pw : U32) + F.shr(x, wb) : U32))))

def ix.fin(+n: U32, s: IX) -> A():
  match s:
    case IX{inp, out, i, x, y}:
      F.pack_cap(out, n)

# one byte per pixel: the index, unbundled
def indices(px: A(), +xs: U32, +ys: U32, +wb: U32) -> A():
  +n = (xs * ys : U32)
  ix.fin(n, ix.loop(U32.to_nat(n), xs, blocks(xs, wb), wb, IX{px, F.new_packed(n), 0, 0, 0}))

def pal_entry(+p: U32) -> U32:
  (chn(p, 2) .|. (chn(p, 1) << 8n : U32) .|. (chn(p, 0) << 16n : U32) .|. (chn(p, 3) << 24n : U32) : U32)

def pal_list(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+p, r}:
      Con{pal_entry(p), pal_list(r)}

def fl.sel(ci: Bool, px: A(), data: A(), +w: U32, +h: U32, +ch: U32, +ok: Bool,
  +kind: U32, +b: U32, +xs: U32, +ys: U32, +size: U32) -> P.IM:
  match ci:
    case True{}:
      P.IM{indices(px, xs, ys, b), w, h, 1, 1, ok,
        List.append(&2, U32, pal_list(F.to_list(data, size)),
          List.replicate(U32, U32.to_nat((256 - size : U32)), 0)), ch}
    case False{}:
      to_image(undo1(U32.to_nat(kind), px, data, b, xs, ys, size), w, h, ch, ok)

def fl.last(tr: TR, px: A(), +w: U32, +h: U32, +ch: U32, +ok: Bool) -> P.IM:
  match tr:
    case TR{+kind, +b, +xs, +ys, +size, data}:
      fl.sel(U32.is_eq(kind, 3), px, data, w, h, ch, ok, kind, b, xs, ys, size)

# undo the transforms; if the last is colour indexing, stop at the indices
def finish(trs: List<&1, TR>, px: A(), +w: U32, +h: U32, +ch: U32, +ok: Bool) -> P.IM:
  match trs:
    case Nil{}:
      to_image(px, w, h, ch, ok)
    case Con{tr, rest}:
      match rest:
        case Nil{}:
          fl.last(tr, px, w, h, ch, ok)
        case Con{r1, r2}:
          finish(Con{r1, r2}, undo.one(tr, px), w, h, ch, ok)

def vp.main(trs: List<&1, TR>, +w: U32, +h: U32, +ch: U32, +ok: Bool, d: DI) -> P.IM:
  match d:
    case DI{inp, pos, px}:
      finish(trs, px, w, h, ch, ok)

def vp.tl(+w: U32, +h: U32, +ch: U32, +ok: Bool, s: TL) -> P.IM:
  match s:
    case TL{inp, +pos, +xs, +ys, trs, go}:
      vp.main(trs, w, h, ch, ok, decode_main(inp, pos, xs, ys))

def vp.av(+sig: U32, +w: U32, +h: U32, br: I.BR) -> P.IM:
  match br:
    case I.BR{inp, +pos, +v}:
      +alpha = U32.is_eq((v .&. 1 : U32), 1)
      +ok = Bool.and(U32.is_eq(sig, 47), U32.is_eq((v >> 1n : U32), 0))
      +w1 = Bool.pick(U32, ok, w, 0)
      +h1 = Bool.pick(U32, ok, h, 0)
      vp.tl(w1, h1, Bool.pick(U32, alpha, 4, 3), ok,
        tl.loop(5n, TL{inp, pos, w1, h1, Nil{}, True{}}))

# 14 bits width - 1, 14 bits height - 1, then 1 bit alpha, 3 bits version
def vp.hdr(+sig: U32, br: I.BR) -> P.IM:
  match br:
    case I.BR{inp, +pos, +v}:
      vp.av(sig, ((v .&. 16383 : U32) + 1 : U32), (((v >> 14n : U32) .&. 16383 : U32) + 1 : U32),
        I.bits(inp, pos, 4))

def vp.sig(br: I.BR) -> P.IM:
  match br:
    case I.BR{inp, +pos, +sig}:
      vp.hdr(sig, I.bits(inp, pos, 28))

# ------------------------------------------------ the RIFF container

def le.d(+x: U32, pr: A() & U32) -> A() & U32:
  (a, +b) = pr
  (a, (x .|. (b << 24n : U32) : U32))

def le.c(+i: U32, +x: U32, pr: A() & U32) -> A() & U32:
  (a, +b) = pr
  le.d((x .|. (b << 16n : U32) : U32), P.rd8(a, (i + 3 : U32)))

def le.b(+i: U32, +x: U32, pr: A() & U32) -> A() & U32:
  (a, +b) = pr
  le.c(i, (x .|. (b << 8n : U32) : U32), P.rd8(a, (i + 2 : U32)))

def le.a(+i: U32, pr: A() & U32) -> A() & U32:
  (a, +x) = pr
  le.b(i, x, P.rd8(a, (i + 1 : U32)))

# the little-endian u32 at byte i
def le32(a: A(), +i: U32) -> A() & U32:
  le.a(i, P.rd8(a, i))

def VP8L() -> U32:
  1278758998

def VP8() -> U32:
  540561494

def ANMF() -> U32:
  1179471425

type WW is Type:
  WW{f: Array<U32>, o: U32, n: U32, at: U32, bad: Bool, go: Bool}

def ww.b(+o: U32, +n: U32, +tag: U32, pr: A() & U32) -> WW:
  (f, +size) = pr
  +lossless = U32.is_eq(tag, VP8L())
  +lossy = Bool.or(U32.is_eq(tag, VP8()), U32.is_eq(tag, ANMF()))
  +o2 = (o + 8 + size + (size .&. 1 : U32) : U32)
  WW{f, o2, n, Bool.pick(U32, lossless, (o + 8 : U32), 0), lossy,
    Bool.and(Bool.not(Bool.or(lossless, lossy)), U32.is_le((o2 + 8 : U32), n))}

def ww.a(+o: U32, +n: U32, pr: A() & U32) -> WW:
  (f, +tag) = pr
  ww.b(o, n, tag, le32(f, (o + 4 : U32)))

def ww.loop(f: Nat, s: WW) -> WW:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case WW{fa, +o, +n, +at, +bad, go}:
          match go:
            case False{}:
              WW{fa, o, n, at, bad, False{}}
            case True{}:
              ww.loop(g, ww.a(o, n, le32(fa, o)))

def wp.sel(found: Bool, f: A(), +at: U32) -> P.IM:
  match found:
    case True{}:
      vp.sig(I.bits(f, (at << 3n : U32), 8))
    case False{}:
      P.IM{Array.new(U32, 1n, 0), 0, 0, 3, 1, False{}, Nil{}, 0}

def wp.b(s: WW) -> P.IM:
  match s:
    case WW{f, o, n, +at, +bad, go}:
      wp.sel(Bool.and(F.lt(0, at), Bool.not(bad)), f, at)

def wp.a(+n: U32, +riff: Bool, pr: A() & U32) -> P.IM:
  (f, +webp) = pr
  wp.b(ww.loop(U32.to_nat(((n / 8 : U32) + 2 : U32)),
    WW{f, 12, n, 0, False{}, Bool.and(riff, U32.is_eq(webp, 1346520407))}))

def wp.r(+n: U32, pr: A() & U32) -> P.IM:
  (f, +riff) = pr
  wp.a(n, U32.is_eq(riff, 1179011410), le32(f, 8))

# Decode a lossless WebP file of n bytes. `ok` is False for lossy or
# animated WebP, and for anything that is not WebP.
def decode(f: A(), +n: U32) -> P.IM:
  wp.r(n, le32(f, 0))

# ------------------------------------------------ any supported file

def any.sel(png: Bool, f: A(), +n: U32) -> P.IM:
  match png:
    case True{}:
      P.decode(f, n)
    case False{}:
      decode(f, n)

def any.a(+n: U32, pr: A() & U32) -> P.IM:
  (f, +sig) = pr
  any.sel(U32.is_eq(sig, 2303741511), f, n)

# PNG or lossless WebP, told apart by their first bytes.
def decode_any(f: A(), +n: U32) -> P.IM:
  any.a(n, P.be32(f, 0))

# ------------------------------------------------ keeping a palette
# When colour indexing is the last transform to undo, the pixels before
# it are palette indices: keep them, with the table, as a PNG palette
# image is kept (1-byte indices, entries r | g << 8 | b << 16 | a << 24).
