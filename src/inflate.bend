import Base
import ./fast.bend as F

# ======================================================================
# zlib/deflate decompression (RFC 1950/1951), for reading PNG.
#
# Input and output are packed chunk arrays: four bytes per slot,
# little-endian. Deflate reads bits least-significant first, so bit k of
# the stream is bit (k mod 32) of slot k/32, and any window of up to 25
# bits is one or two reads.
#
# Huffman codes decode through a 10-bit table; longer codes fall back to
# reading one bit at a time (as zlib's puff.c does). All tables live in
# one 8192-slot work array `h`:
#
#   [0, 16)      litlen count[len]     [16, 304)    litlen symbols, sorted
#   [320, 336)   dist count[len]       [336, 368)   dist symbols, sorted
#   [368, 384)   clen count[len]       [384, 416)   clen symbols, sorted
#   [416, 432)   offsets (scratch)     [432, 448)   next code (scratch)
#   [448, 768)   code lengths          [800, 819)   clen code lengths
#   [832, 861)   length base           [864, 893)   length extra bits
#   [896, 926)   distance base         [928, 958)   distance extra bits
#   [1024, 2048) litlen table          [2048, 3072) dist table
#   [3072, 4096) clen table
# A table entry is (sym << 4) | len, or 0 for a code longer than 10 bits.
# ======================================================================

def A() -> Type:
  Array<U32>

def LC() -> U32:
  0

def LS() -> U32:
  16

def DC() -> U32:
  320

def DS() -> U32:
  336

def CC() -> U32:
  368

def CS() -> U32:
  384

def OFF() -> U32:
  416

def NC() -> U32:
  432

def LENS() -> U32:
  448

def CLL() -> U32:
  800

def LB() -> U32:
  832

def LX() -> U32:
  864

def DB() -> U32:
  896

def DX() -> U32:
  928

def LP() -> U32:
  1024

def DP() -> U32:
  2048

def CP() -> U32:
  3072

def mask(+n: U32) -> U32:
  (F.shl(1, n) - 1 : U32)

# ------------------------------------------------ bits, LSB first

type BR is Type:
  BR{a: Array<U32>, pos: U32, v: U32}

def bits.c(+pos: U32, +n: U32, +lo: U32, pr: A() & U32) -> BR:
  (a, +hi) = pr
  +s = (pos .&. 31 : U32)
  +w = Bool.pick(U32, U32.is_eq(s, 0), lo,
    (F.shr(lo, s) .|. F.shl(hi, ((32 - s : U32) .&. 31 : U32)) : U32))
  BR{a, (pos + n : U32), (w .&. mask(n) : U32)}

def bits.b(+pos: U32, +n: U32, pr: A() & U32) -> BR:
  (a, +lo) = pr
  bits.c(pos, n, lo, F.get(a, ((pos >> 5n : U32) + 1 : U32)))

# the n (<= 25) bits at bit `pos`, first bit lowest
def bits(a: A(), +pos: U32, +n: U32) -> BR:
  bits.b(pos, n, F.get(a, (pos >> 5n : U32)))

# ------------------------------------------------ small array loops

def fill(f: Nat, +at: U32, +v: U32, h: A()) -> A():
  match f:
    case 0n:
      h
    case 1n+g:
      fill(g, (at + 1 : U32), v, Array.set(U32, h, at, v))

def put_list(xs: List<&2, U32>, +at: U32, h: A()) -> A():
  match xs:
    case Nil{}:
      h
    case Con{+x, r}:
      put_list(r, (at + 1 : U32), Array.set(U32, h, at, x))

# the low `n` bits of c, reversed (codes are MSB-first, the stream LSB-first)
def rev(f: Nat, +c: U32, +r: U32) -> U32:
  match f:
    case 0n:
      r
    case 1n+g:
      rev(g, (c >> 1n : U32), ((r << 1n : U32) .|. (c .&. 1 : U32) : U32))

# ------------------------------------------------ building a code
# From code lengths h[lens + s], s < n: count[len], the symbols sorted by
# (len, sym), and the 10-bit table. `cnt`, `sym`, `pri` are offsets.

def counts.b(+cnt: U32, pr: A() & U32) -> A():
  (h, +l) = pr
  F.inc(h, (cnt + l : U32))

def counts(f: Nat, +lens: U32, +cnt: U32, +s: U32, h: A()) -> A():
  match f:
    case 0n:
      h
    case 1n+g:
      counts(g, lens, cnt, (s + 1 : U32), counts.b(cnt, F.get(h, (lens + s : U32))))

# off[l] = off[l-1] + cnt[l-1];  next[l] = (next[l-1] + cnt[l-1]) << 1
def starts.c(+l: U32, +o: U32, r: F.R2) -> A():
  match r:
    case F.R2{h, +nx, +c}:
      Array.set(U32, Array.set(U32, h, (OFF() + l : U32), (o + c : U32)),
        (NC() + l : U32), ((nx + c : U32) << 1n : U32))

def starts.b(+cnt: U32, +l: U32, r: F.R2) -> A():
  match r:
    case F.R2{h, +o, +nx}:
      starts.c(l, o, F.get2(h, (NC() + l - 1 : U32), (cnt + l - 1 : U32)))

def starts(f: Nat, +cnt: U32, +l: U32, h: A()) -> A():
  match f:
    case 0n:
      h
    case 1n+g:
      starts(g, cnt, (l + 1 : U32), starts.b(cnt, l,
        F.get2(h, (OFF() + l - 1 : U32), (NC() + l - 1 : U32))))

# table[rev(code) + k * 2^len] := (s << 4) | len, for every k < 2^(10-len)
def spread(f: Nat, +at: U32, +step: U32, +e: U32, h: A()) -> A():
  match f:
    case 0n:
      h
    case 1n+g:
      spread(g, (at + step : U32), step, e, Array.set(U32, h, at, e))

def asn.e(short: Bool, +pb: U32, +s: U32, +l: U32, +pri: U32, +c: U32, h: A()) -> A():
  match short:
    case False{}:
      h
    case True{}:
      spread(U32.to_nat(F.shl(1, (pb - l : U32))),
        (pri + rev(U32.to_nat(l), c, 0) : U32), F.shl(1, l),
        ((s << 4n : U32) .|. l : U32), h)

def asn.d(+pb: U32, +s: U32, +l: U32, +pri: U32, +c: U32, h: A()) -> A():
  asn.e(U32.is_le(l, pb), pb, s, l, pri, c, h)

def asn.c(+pb: U32, +s: U32, +l: U32, +sym: U32, +pri: U32, +i: U32, r: A() & U32) -> A():
  (h, +c) = r
  asn.d(pb, s, l, pri, c, Array.set(U32, Array.set(U32, Array.set(U32, h,
    (OFF() + l : U32), (i + 1 : U32)), (sym + i : U32), s),
    (NC() + l : U32), (c + 1 : U32)))

def asn.b(+pb: U32, +s: U32, +l: U32, +sym: U32, +pri: U32, r: A() & U32) -> A():
  (h, +i) = r
  asn.c(pb, s, l, sym, pri, i, F.get(h, (NC() + l : U32)))

def asn.sel(skip: Bool, +pb: U32, +s: U32, +l: U32, +sym: U32, +pri: U32, h: A()) -> A():
  match skip:
    case True{}:
      h
    case False{}:
      asn.b(pb, s, l, sym, pri, F.get(h, (OFF() + l : U32)))

def asn.a(+pb: U32, +s: U32, +sym: U32, +pri: U32, r: A() & U32) -> A():
  (h, +l) = r
  asn.sel(U32.is_eq(l, 0), pb, s, l, sym, pri, h)

def assign(f: Nat, +pb: U32, +lens: U32, +sym: U32, +pri: U32, +s: U32, h: A()) -> A():
  match f:
    case 0n:
      h
    case 1n+g:
      assign(g, pb, lens, sym, pri, (s + 1 : U32),
        asn.a(pb, s, sym, pri, F.get(h, (lens + s : U32))))

# with a 2^pb-entry table (deflate uses 10 bits; WebP's larger alphabets 12)
def build_w(h: A(), +pb: U32, +lens: U32, +n: U32, +cnt: U32, +sym: U32, +pri: U32) -> A():
  assign(U32.to_nat(n), pb, lens, sym, pri, 0,
    starts(15n, cnt, 1,
      Array.set(U32, counts(U32.to_nat(n), lens, cnt, 0,
        fill(16n, OFF(), 0, fill(16n, NC(), 0, fill(U32.to_nat(F.shl(1, pb)), pri, 0,
          fill(16n, cnt, 0, h))))), cnt, 0)))

def build(h: A(), +lens: U32, +n: U32, +cnt: U32, +sym: U32, +pri: U32) -> A():
  build_w(h, 10, lens, n, cnt, sym, pri)

# ------------------------------------------------ one symbol

type DY is Type:
  DY{h: Array<U32>, inp: Array<U32>, pos: U32, sym: U32}

type PF is Type:
  PF{h: Array<U32>, inp: Array<U32>, pos: U32, code: U32, first: U32,
    index: U32, len: U32, sym: U32, go: Bool}

def pf.hit(inp: A(), +pos: U32, pr: A() & U32) -> PF:
  (h, +sym) = pr
  PF{h, inp, pos, 0, 0, 0, 0, sym, False{}}

def pf.sel(hit: Bool, h: A(), inp: A(), +pos: U32, +code: U32, +first: U32,
  +index: U32, +len: U32, +count: U32, +sym: U32) -> PF:
  match hit:
    case True{}:
      pf.hit(inp, pos, F.get(h, (sym + index + code - first : U32)))
    case False{}:
      PF{h, inp, pos, (code << 1n : U32), ((first + count : U32) << 1n : U32),
        (index + count : U32), (len + 1 : U32), 0, True{}}

def pf.c(inp: A(), +pos: U32, +code: U32, +first: U32, +index: U32,
  +len: U32, +sym: U32, pr: A() & U32) -> PF:
  (h, +count) = pr
  pf.sel(F.lt((code - first : U32), count), h, inp, pos, code, first, index,
    len, count, sym)

def pf.b(h: A(), +cnt: U32, +sym: U32, +code: U32, +first: U32,
  +index: U32, +len: U32, b: BR) -> PF:
  match b:
    case BR{inp, +pos, +v}:
      +c1 = (code .|. v : U32)
      pf.c(inp, pos, c1, first, index, len, sym, F.get(h, (cnt + len : U32)))

def pf.loop(f: Nat, +cnt: U32, +sym: U32, s: PF) -> PF:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case PF{h, inp, +pos, +code, +first, +index, +len, +sy, go}:
          match go:
            case False{}:
              PF{h, inp, pos, code, first, index, len, sy, False{}}
            case True{}:
              pf.loop(g, cnt, sym, pf.b(h, cnt, sym, code, first, index, len,
                bits(inp, pos, 1)))

def pf.fin(s: PF) -> DY:
  match s:
    case PF{h, inp, pos, code, first, index, len, sym, go}:
      DY{h, inp, pos, sym}

def dec.sel(hit: Bool, h: A(), inp: A(), +pos: U32, +e: U32, +cnt: U32,
  +sym: U32) -> DY:
  match hit:
    case True{}:
      DY{h, inp, (pos + (e .&. 15 : U32) : U32), (e >> 4n : U32)}
    case False{}:
      pf.fin(pf.loop(16n, cnt, sym, PF{h, inp, pos, 0, 0, 0, 1, 0, True{}}))

def dec.b(inp: A(), +pos: U32, +cnt: U32, +sym: U32, pr: A() & U32) -> DY:
  (h, +e) = pr
  dec.sel(U32.is_ne(e, 0), h, inp, pos, e, cnt, sym)

def dec.a(h: A(), +pos: U32, +cnt: U32, +sym: U32, +pri: U32, b: BR) -> DY:
  match b:
    case BR{inp, p, +v}:
      dec.b(inp, pos, cnt, sym, F.get(h, (pri + v : U32)))

# the next symbol of the code at (cnt, sym, pri), with a 2^pb-entry table
def decode_w(h: A(), inp: A(), +pos: U32, +pb: U32, +cnt: U32, +sym: U32, +pri: U32) -> DY:
  dec.a(h, pos, cnt, sym, pri, bits(inp, pos, pb))

def decode(h: A(), inp: A(), +pos: U32, +cnt: U32, +sym: U32, +pri: U32) -> DY:
  decode_w(h, inp, pos, 10, cnt, sym, pri)

# ------------------------------------------------ inflate state

type IS is Type:
  IS{inp: Array<U32>, out: Array<U32>, h: Array<U32>, pos: U32, opos: U32,
    go: Bool}

# ------------------------------------------------ the symbol loop

type SS is Type:
  SS{inp: Array<U32>, out: Array<U32>, h: Array<U32>, pos: U32, opos: U32,
    go: Bool}

def ss.copy(inp: A(), h: A(), +pos: U32, c: F.CP) -> SS:
  match c:
    case F.CP{out, +opos, d}:
      SS{inp, out, h, pos, opos, True{}}

def ss.d3(out: A(), h: A(), +opos: U32, +len: U32, +db: U32, b: BR) -> SS:
  match b:
    case BR{inp, +pos, +v}:
      ss.copy(inp, h, pos, F.cp.loop(U32.to_nat(len), F.CP{out, opos, (db + v : U32)}))

def ss.d2(inp: A(), out: A(), +pos: U32, +opos: U32, +len: U32, r: F.R2) -> SS:
  match r:
    case F.R2{h, +db, +dx}:
      ss.d3(out, h, opos, len, db, bits(inp, pos, dx))

def ss.d1(out: A(), +opos: U32, +len: U32, d: DY) -> SS:
  match d:
    case DY{h, inp, +pos, +di}:
      ss.d2(inp, out, pos, opos, len, F.get2(h, (DB() + di : U32), (DX() + di : U32)))

def ss.l2(out: A(), h: A(), +opos: U32, +lb: U32, b: BR) -> SS:
  match b:
    case BR{inp, +pos, +v}:
      ss.d1(out, opos, (lb + v : U32), decode(h, inp, pos, DC(), DS(), DP()))

def ss.l1(inp: A(), out: A(), +pos: U32, +opos: U32, r: F.R2) -> SS:
  match r:
    case F.R2{h, +lb, +lx}:
      ss.l2(out, h, opos, lb, bits(inp, pos, lx))

def ss.kind(lit: Bool, stop: Bool, inp: A(), out: A(), h: A(), +pos: U32,
  +opos: U32, +sym: U32) -> SS:
  match lit:
    case True{}:
      SS{inp, F.set_byte(out, opos, sym), h, pos, (opos + 1 : U32), True{}}
    case False{}:
      match stop:
        case True{}:
          SS{inp, out, h, pos, opos, False{}}
        case False{}:
          +li = (sym - 257 : U32)
          ss.l1(inp, out, pos, opos, F.get2(h, (LB() + li : U32), (LX() + li : U32)))

def ss.b(out: A(), +opos: U32, d: DY) -> SS:
  match d:
    case DY{h, inp, +pos, +sym}:
      ss.kind(F.lt(sym, 256), U32.is_eq(sym, 256), inp, out, h, pos, opos, sym)

def ss.loop(f: Nat, s: SS) -> SS:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case SS{inp, out, h, +pos, +opos, go}:
          match go:
            case False{}:
              SS{inp, out, h, pos, opos, False{}}
            case True{}:
              ss.loop(g, ss.b(out, opos, decode(h, inp, pos, LC(), LS(), LP())))

# after a block: continue unless it was the last
def ss.fin(+last: Bool, s: SS) -> IS:
  match s:
    case SS{inp, out, h, +pos, +opos, go}:
      IS{inp, out, h, pos, opos, Bool.not(last)}

def symbols(+last: Bool, inp: A(), out: A(), h: A(), +pos: U32, +opos: U32,
  +olen: U32) -> IS:
  ss.fin(last, ss.loop(U32.to_nat((olen - opos + 1 : U32)),
    SS{inp, out, h, pos, opos, True{}}))

# ------------------------------------------------ stored blocks

type CB is Type:
  CB{inp: Array<U32>, out: Array<U32>, q: U32, opos: U32}

def cb.b(out: A(), +q: U32, +opos: U32, pr: A() & U32) -> CB:
  (inp, +w) = pr
  CB{inp, F.set_byte(out, opos, F.byte_of(w, q)), (q + 1 : U32), (opos + 1 : U32)}

def cb.loop(f: Nat, s: CB) -> CB:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CB{inp, out, +q, +opos}:
          cb.loop(g, cb.b(out, q, opos, F.get(inp, (q >> 2n : U32))))

def cb.fin(+last: Bool, h: A(), +pos: U32, c: CB) -> IS:
  match c:
    case CB{inp, out, q, +opos}:
      IS{inp, out, h, pos, opos, Bool.not(last)}

def stored.b(+last: Bool, out: A(), h: A(), +p: U32, +opos: U32, b: BR) -> IS:
  match b:
    case BR{inp, q, +len}:
      +start = ((p + 32 : U32) >> 3n : U32)
      cb.fin(last, h, (p + 32 + (len << 3n : U32) : U32),
        cb.loop(U32.to_nat(len), CB{inp, out, start, opos}))

def stored(+last: Bool, inp: A(), out: A(), h: A(), +pos: U32, +opos: U32) -> IS:
  +p = ((pos + 7 : U32) .&. 4294967288 : U32)
  stored.b(last, out, h, p, opos, bits(inp, p, 16))

# ------------------------------------------------ fixed codes

def fixed(+last: Bool, inp: A(), out: A(), h: A(), +pos: U32, +opos: U32,
  +olen: U32) -> IS:
  symbols(last, inp, out,
    build(build(fill(30n, (LENS() + 288 : U32), 5,
      fill(8n, (LENS() + 280 : U32), 8, fill(24n, (LENS() + 256 : U32), 7,
        fill(112n, (LENS() + 144 : U32), 9, fill(144n, LENS(), 8, h))))),
      LENS(), 288, LC(), LS(), LP()),
      (LENS() + 288 : U32), 30, DC(), DS(), DP()),
    pos, opos, olen)

# ------------------------------------------------ dynamic codes

# The code-length code's lengths arrive in this order, 3 bits each.
def CLORDER() -> List<&2, U32>:
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

type CR is Type:
  CR{inp: Array<U32>, h: Array<U32>, pos: U32}

def cr.b(+o: U32, h: A(), b: BR) -> CR:
  match b:
    case BR{inp, +pos, +v}:
      CR{inp, Array.set(U32, h, (CLL() + o : U32), v), pos}

def cr.step(+o: U32, s: CR) -> CR:
  match s:
    case CR{inp, h, +pos}:
      cr.b(o, h, bits(inp, pos, 3))

def clens(f: Nat, xs: List<&2, U32>, s: CR) -> CR:
  match f:
    case 0n:
      s
    case 1n+g:
      match xs:
        case Nil{}:
          s
        case Con{+o, r}:
          clens(g, r, cr.step(o, s))

# The literal/length and distance code lengths, one symbol of the
# code-length code at a time. A plain length is "repeat once, no extra
# bits", which makes 16 (repeat the previous), 17 and 18 (zeros) the same
# step with different numbers.
type CL is Type:
  CL{inp: Array<U32>, h: Array<U32>, pos: U32, i: U32, prev: U32,
    total: U32, go: Bool}

def cl.c(h: A(), +i: U32, +total: U32, +base: U32, +val: U32, b: BR) -> CL:
  match b:
    case BR{inp, +pos, +v}:
      +r = (base + v : U32)
      +i1 = (i + r : U32)
      CL{inp, fill(U32.to_nat(r), (LENS() + i : U32), val, h), pos, i1, val,
        total, F.lt(i1, total)}

def cl.b(+i: U32, +prev: U32, +total: U32, d: DY) -> CL:
  match d:
    case DY{h, inp, +pos, +sym}:
      +small = F.lt(sym, 16)
      +w = Bool.pick(U32, small, 0, Bool.pick(U32, U32.is_eq(sym, 16), 2,
        Bool.pick(U32, U32.is_eq(sym, 17), 3, 7)))
      +base = Bool.pick(U32, small, 1, Bool.pick(U32, U32.is_eq(sym, 18), 11, 3))
      +val = Bool.pick(U32, small, sym, Bool.pick(U32, U32.is_eq(sym, 16), prev, 0))
      cl.c(h, i, total, base, val, bits(inp, pos, w))

def cl.loop(f: Nat, s: CL) -> CL:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CL{inp, h, +pos, +i, +prev, +total, go}:
          match go:
            case False{}:
              CL{inp, h, pos, i, prev, total, False{}}
            case True{}:
              cl.loop(g, cl.b(i, prev, total, decode(h, inp, pos, CC(), CS(), CP())))

def dyn.c(+last: Bool, out: A(), +opos: U32, +olen: U32, +hlit: U32,
  +hdist: U32, s: CL) -> IS:
  match s:
    case CL{inp, h, +pos, i, prev, total, go}:
      symbols(last, inp, out,
        build(build(h, LENS(), hlit, LC(), LS(), LP()),
          (LENS() + hlit : U32), hdist, DC(), DS(), DP()),
        pos, opos, olen)

def dyn.b(+last: Bool, out: A(), +opos: U32, +olen: U32, +hlit: U32,
  +hdist: U32, s: CR) -> IS:
  match s:
    case CR{inp, h, +pos}:
      +total = (hlit + hdist : U32)
      dyn.c(last, out, opos, olen, hlit, hdist,
        cl.loop(U32.to_nat(total), CL{inp, build(h, CLL(), 19, CC(), CS(), CP()),
          pos, 0, 0, total, F.lt(0, total)}))

def dyn.a(+last: Bool, out: A(), h: A(), +opos: U32, +olen: U32, b: BR) -> IS:
  match b:
    case BR{inp, +pos, +v}:
      +hclen = (((v >> 10n : U32) .&. 15 : U32) + 4 : U32)
      dyn.b(last, out, opos, olen, ((v .&. 31 : U32) + 257 : U32),
        (((v >> 5n : U32) .&. 31 : U32) + 1 : U32),
        clens(U32.to_nat(hclen), CLORDER(), CR{inp, fill(19n, CLL(), 0, h), pos}))

def dynamic(+last: Bool, inp: A(), out: A(), h: A(), +pos: U32, +opos: U32,
  +olen: U32) -> IS:
  dyn.a(last, out, h, opos, olen, bits(inp, pos, 14))

# ------------------------------------------------ blocks

def blk.sel(t0: Bool, t1: Bool, t2: Bool, +last: Bool, inp: A(), out: A(),
  h: A(), +pos: U32, +opos: U32, +olen: U32) -> IS:
  match t0:
    case True{}:
      stored(last, inp, out, h, pos, opos)
    case False{}:
      match t1:
        case True{}:
          fixed(last, inp, out, h, pos, opos, olen)
        case False{}:
          match t2:
            case True{}:
              dynamic(last, inp, out, h, pos, opos, olen)
            case False{}:
              IS{inp, out, h, pos, opos, False{}}

def blk.b(out: A(), h: A(), +opos: U32, +olen: U32, b: BR) -> IS:
  match b:
    case BR{inp, +pos, +v}:
      +t = (v >> 1n : U32)
      blk.sel(U32.is_eq(t, 0), U32.is_eq(t, 1), U32.is_eq(t, 2),
        U32.is_eq((v .&. 1 : U32), 1), inp, out, h, pos, opos, olen)

def blk.loop(f: Nat, +olen: U32, s: IS) -> IS:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case IS{inp, out, h, +pos, +opos, go}:
          match go:
            case False{}:
              IS{inp, out, h, pos, opos, False{}}
            case True{}:
              blk.loop(g, olen, blk.b(out, h, opos, olen, bits(inp, pos, 3)))

def infl.fin(+cap: U32, s: IS) -> A():
  match s:
    case IS{inp, out, h, pos, +opos, go}:
      Array.set(U32, out, (cap - 1 : U32), opos)

# Inflate the deflate stream that starts at bit `start` of `inp`, into a
# packed array of at least `olen` bytes (the count, as decoded, in the
# last slot).
def inflate(inp: A(), +start: U32, +olen: U32) -> A():
  +d = F.depth(32n, 1n, ((olen >> 2n : U32) + 2 : U32))
  +cap = U32.pow(2, d)
  infl.fin(cap, blk.loop(U32.to_nat((olen + 2 : U32)), olen, IS{inp,
    Array.new(U32, d, 0),
    put_list(F.DEXT(), DX(), put_list(F.DBASE(), DB(), put_list(F.LEXT(), LX(),
      put_list(F.LBASE(), LB(), Array.new(U32, 13n, 0))))),
    start, 0, True{}}))
