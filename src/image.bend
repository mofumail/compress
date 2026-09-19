import Base
import ./fast.bend as F
import ./png.bend as P
import ./atree.bend as T

# ======================================================================
# The image codec (.bzi).
#
# An image is split into horizontal strips. Each strip is filtered (per
# row, the best of PNG's five filters) and LZ77-parsed in parallel; the
# symbol counts of all strips are summed into ONE Huffman code; then
# every strip is encoded with that code, again in parallel. One shared
# code keeps the per-strip overhead at 8 bytes, so an image can be cut
# into the ~256 pieces Bend's scheduler needs to use every core.
#
# File:   "BZI1" | width | height | rows per strip  (u32 big-endian each)
#         | channels (1) | bytes per sample (1) | palette channels (1) | 0
#         | 320 code lengths (1 byte each)                 = 340 bytes
#         then, for a palette image (palette channels 3 or 4, and the
#         pixels are 1-byte indices): 1024 (u32) | 0 (u32) | 256 entries
#         of r, g, b, a
#         then per strip: payload bytes (u32) | symbol bits (u32) | payload
# The payload is the fast codec's bitstream (src/fast.bend): symbol codes,
# then extra bits. Strips decode on their own, back to exact pixels.
# ======================================================================

def A() -> Type:
  Array<U32>

def HDR() -> U32:
  340

# ------------------------------------------------ splitting into strips
# `len` bytes from byte `off` of `src`, a word at a time: word k of the
# copy is spliced from the two source slots it straddles.

type SC is Type:
  SC{src: Array<U32>, dst: Array<U32>, k: U32}

def sc.c(dst: A(), +k: U32, +s: U32, +w0: U32, pr: A() & U32) -> SC:
  (src, +w1) = pr
  SC{src, Array.set(U32, dst, k, Bool.pick(U32, U32.is_eq(s, 0), w0,
    (F.shr(w0, s) .|. F.shl(w1, ((32 - s : U32) .&. 31 : U32)) : U32))), (k + 1 : U32)}

def sc.b(dst: A(), +k: U32, +s: U32, +at: U32, pr: A() & U32) -> SC:
  (src, +w0) = pr
  sc.c(dst, k, s, w0, F.get(src, (at + 1 : U32)))

def sc.loop(f: Nat, +off: U32, s: SC) -> SC:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case SC{src, dst, +k}:
          +at = ((off >> 2n : U32) + k : U32)
          sc.loop(g, off, sc.b(dst, k, ((off .&. 3 : U32) << 3n : U32), at,
            F.get(src, at)))

type SP is Type:
  SP{src: Array<U32>, i: U32, acc: List<&1, Array<U32>>}

def sp.b(+i: U32, +len: U32, acc: List<&1, A()>, s: SC) -> SP:
  match s:
    case SC{src, dst, k}:
      SP{src, (i + 1 : U32), Con{F.pack_cap(dst, len), acc}}

def sp.loop(f: Nat, +total: U32, +sb: U32, s: SP) -> SP:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case SP{src, +i, acc}:
          +off = (i * sb : U32)
          +len = U32.min(sb, (total - off : U32))
          sp.loop(g, total, sb, sp.b(i, len, acc,
            sc.loop(U32.to_nat(((len + 3 : U32) >> 2n : U32)), off,
              SC{src, F.new_packed(len), 0})))

def sp.fin(s: SP) -> List<&1, A()>:
  match s:
    case SP{src, i, acc}:
      List.reverse(&1, Array<U32>, acc)

# `total` bytes cut into pieces of `sb` bytes (the last may be shorter)
def split(px: A(), +total: U32, +sb: U32, +count: U32) -> List<&1, A()>:
  sp.fin(sp.loop(U32.to_nat(count), total, sb, SP{px, 0, Nil{}}))

# ------------------------------------------------ filtering
# The neighbourhood of byte i of a row starting at `base`: the byte, and
# its left (a), up (b) and up-left (c) neighbours, 0 outside the image.

type NB is Type:
  NB{p: Array<U32>, x: U32, a: U32, b: U32, c: U32}

def nb.d(+left: Bool, +up: Bool, +x: U32, +a: U32, +b: U32, pr: A() & U32) -> NB:
  (p, +c) = pr
  NB{p, x, Bool.pick(U32, left, a, 0), Bool.pick(U32, up, b, 0),
    Bool.pick(U32, Bool.and(left, up), c, 0)}

def nb.c(+at: U32, +rb: U32, +bpp: U32, +left: Bool, +up: Bool, +x: U32,
  +a: U32, pr: A() & U32) -> NB:
  (p, +b) = pr
  nb.d(left, up, x, a, b, P.rd8(p, (at - rb - bpp : U32)))

def nb.b(+at: U32, +rb: U32, +bpp: U32, +left: Bool, +up: Bool, +x: U32,
  pr: A() & U32) -> NB:
  (p, +a) = pr
  nb.c(at, rb, bpp, left, up, x, a, P.rd8(p, (at - rb : U32)))

def nb.a(+at: U32, +rb: U32, +bpp: U32, +left: Bool, +up: Bool,
  pr: A() & U32) -> NB:
  (p, +x) = pr
  nb.b(at, rb, bpp, left, up, x, P.rd8(p, (at - bpp : U32)))

def around(p: A(), +at: U32, +i: U32, +rb: U32, +bpp: U32, +up: Bool) -> NB:
  nb.a(at, rb, bpp, U32.is_le(bpp, i), up, P.rd8(p, at))

# a residual's size as a signed byte
def cost(+r: U32) -> U32:
  U32.min(r, (256 - r : U32))

def res(+t: U32, n: NB) -> A() & U32:
  match n:
    case NB{p, +x, +a, +b, +c}:
      (p, ((x - P.pred(t, a, b, c) : U32) .&. 255 : U32))

# pass 1: the summed cost of each of the five filters over one row
type FC is Type:
  FC{p: Array<U32>, i: U32, s0: U32, s1: U32, s2: U32, s3: U32, s4: U32}

def fc.b(+i: U32, +s0: U32, +s1: U32, +s2: U32, +s3: U32, +s4: U32, n: NB) -> FC:
  match n:
    case NB{p, +x, +a, +b, +c}:
      FC{p, (i + 1 : U32),
        (s0 + cost(x) : U32),
        (s1 + cost(((x - a : U32) .&. 255 : U32)) : U32),
        (s2 + cost(((x - b : U32) .&. 255 : U32)) : U32),
        (s3 + cost(((x - P.pred(3, a, b, c) : U32) .&. 255 : U32)) : U32),
        (s4 + cost(((x - P.pred(4, a, b, c) : U32) .&. 255 : U32)) : U32)}

def fc.loop(f: Nat, +base: U32, +rb: U32, +bpp: U32, +up: Bool, s: FC) -> FC:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case FC{p, +i, +s0, +s1, +s2, +s3, +s4}:
          fc.loop(g, base, rb, bpp, up, fc.b(i, s0, s1, s2, s3, s4,
            around(p, (base + i : U32), i, rb, bpp, up)))

def best(+s0: U32, +s1: U32, +s2: U32, +s3: U32, +s4: U32) -> U32:
  +m01 = U32.min(s0, s1)
  +m23 = U32.min(s2, s3)
  +m = U32.min(U32.min(m01, m23), s4)
  Bool.pick(U32, U32.is_eq(m, s0), 0, Bool.pick(U32, U32.is_eq(m, s1), 1,
    Bool.pick(U32, U32.is_eq(m, s2), 2, Bool.pick(U32, U32.is_eq(m, s3), 3, 4))))

# pass 2: the chosen filter's residuals
type FE is Type:
  FE{p: Array<U32>, out: Array<U32>, i: U32, opos: U32}

def fe.b(out: A(), +i: U32, +opos: U32, pr: A() & U32) -> FE:
  (p, +r) = pr
  FE{p, F.set_byte(out, opos, r), (i + 1 : U32), (opos + 1 : U32)}

def fe.loop(f: Nat, +t: U32, +base: U32, +rb: U32, +bpp: U32, +up: Bool,
  s: FE) -> FE:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case FE{p, out, +i, +opos}:
          fe.loop(g, t, base, rb, bpp, up, fe.b(out, i, opos,
            res(t, around(p, (base + i : U32), i, rb, bpp, up))))

type FR is Type:
  FR{p: Array<U32>, out: Array<U32>, row: U32, opos: U32}

def fr.c(+row: U32, s: FE) -> FR:
  match s:
    case FE{p, out, i, +opos}:
      FR{p, out, (row + 1 : U32), opos}

def fr.b(out: A(), +row: U32, +opos: U32, +rb: U32, +bpp: U32, +none: Bool,
  s: FC) -> FR:
  match s:
    case FC{p, i, +s0, +s1, +s2, +s3, +s4}:
      +t = Bool.pick(U32, none, 0, best(s0, s1, s2, s3, s4))
      fr.c(row, fe.loop(U32.to_nat(rb), t, (row * rb : U32), rb, bpp, F.lt(0, row),
        FE{p, F.set_byte(out, opos, t), 0, (opos + 1 : U32)}))

def fr.loop(f: Nat, +rb: U32, +bpp: U32, +none: Bool, s: FR) -> FR:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case FR{p, out, +row, +opos}:
          fr.loop(g, rb, bpp, none, fr.b(out, row, opos, rb, bpp, none,
            fc.loop(U32.to_nat(rb), (row * rb : U32), rb, bpp, F.lt(0, row),
              FC{p, 0, 0, 0, 0, 0, 0})))

def fr.fin(+len: U32, s: FR) -> A():
  match s:
    case FR{p, out, row, opos}:
      F.pack_cap(out, len)

# `rows` rows of `rb` bytes, each written as a filter type byte and the
# row filtered with it -- exactly PNG's scanline layout. With `none`
# (palette indices, where differences mean nothing) every row is left
# unfiltered, as PNG encoders do.
def filter(p: A(), +rows: U32, +rb: U32, +bpp: U32, +none: Bool) -> A():
  +len = (rows * (rb + 1 : U32) : U32)
  fr.fin(len, fr.loop(U32.to_nat(rows), rb, bpp, none, FR{p, F.new_packed(len), 0, 0}))

# ------------------------------------------------ slot copies

type CY is Type:
  CY{src: Array<U32>, dst: Array<U32>, i: U32}

def cy.b(dst: A(), +i: U32, +d0: U32, pr: A() & U32) -> CY:
  (src, +v) = pr
  CY{src, Array.set(U32, dst, (d0 + i : U32), v), (i + 1 : U32)}

def cy.loop(f: Nat, +s0: U32, +d0: U32, s: CY) -> CY:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CY{src, dst, +i}:
          cy.loop(g, s0, d0, cy.b(dst, i, d0, F.get(src, (s0 + i : U32))))

def cy.dst(s: CY) -> A():
  match s:
    case CY{src, dst, i}:
      dst

# ------------------------------------------------ phase A: filter and parse
# A strip's pixels in; out: one array holding the strip's symbol counts
# [0, 320), its token count [320], its filtered length [321] and its
# tokens from [322].

def TOK() -> U32:
  322

# Hash-chain depth for image data. Deeper than the text codec's 8:
# filtered pixels reward it more (about 4% smaller at 32), and the cost
# runs in parallel.
def CHAIN() -> Nat:
  32n

def pa.c(+nt: U32, +n: U32, freq: A(), tok: A()) -> A():
  cy.dst(cy.loop(U32.to_nat(nt), 0, TOK(), CY{tok,
    Array.set(U32, Array.set(U32, cy.dst(cy.loop(320n, 0, 0, CY{freq,
      Array.new(U32, F.depth(32n, 1n, (TOK() + nt + 1 : U32)), 0), 0})),
      320, nt), 321, n), 0}))

def pa.b(+n: U32, s: F.PS) -> A():
  match s:
    case F.PS{w, head, prev, tok, freq, t, n0, pos, +nt, more}:
      pa.c(nt, n, freq, tok)

def pa.a(+rb: U32, +bpp: U32, +none: Bool, pr: A() & U32) -> A():
  (p, +cnt) = pr
  +rows = Bool.pick(U32, U32.is_eq(rb, 0), 0, (cnt / U32.max(rb, 1) : U32))
  +n = (rows * (rb + 1 : U32) : U32)
  pa.b(n, F.parse_chain(F.win(filter(p, rows, rb, bpp, none), n), n, CHAIN()))

def phase_a(p: A(), +rb: U32, +bpp: U32, +none: Bool) -> A():
  pa.a(rb, bpp, none, F.arr_len(p))

# ------------------------------------------------ one code for all strips

type AD is Type:
  AD{c: Array<U32>, g: Array<U32>, i: U32}

def ad.c(c: A(), +i: U32, +v: U32, pr: A() & U32) -> AD:
  (g, +u) = pr
  AD{c, Array.set(U32, g, i, (u + v : U32)), (i + 1 : U32)}

def ad.b(g: A(), +i: U32, pr: A() & U32) -> AD:
  (c, +v) = pr
  ad.c(c, i, v, F.get(g, i))

def ad.loop(f: Nat, s: AD) -> AD:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case AD{c, gl, +i}:
          ad.loop(g, ad.b(gl, i, F.get(c, i)))

type GS is Type:
  GS{g: Array<U32>, kept: List<&1, Array<U32>>}

def gs.b(kept: List<&1, A()>, s: AD) -> GS:
  match s:
    case AD{c, g, i}:
      GS{g, Con{c, kept}}

def gs.add(c: A(), s: GS) -> GS:
  match s:
    case GS{g, kept}:
      gs.b(kept, ad.loop(320n, AD{c, g, 0}))

# the strips' counts summed; the strips kept, in reverse order
def gather(xs: List<&1, A()>, s: GS) -> GS:
  match xs:
    case Nil{}:
      s
    case Con{c, r}:
      gather(r, gs.add(c, s))

# ------------------------------------------------ phase C: encode

def pc.passb(e: F.ES) -> F.ES:
  match e:
    case F.ES{tok, l, w, k, +nt, bits, pb, go}:
      F.es.loop(U32.to_nat((nt - TOK() : U32)),
        F.ES{tok, l, w, TOK(), nt, bits, True{}, F.lt(TOK(), nt)})

def pc.out(+bits: U32, w: F.W) -> A():
  match w:
    case F.W{out, acc, nacc, +opos}:
      F.pack_le(F.put_list(F.u32be((opos - 8 : U32), F.u32be(bits, Nil{})), 0, out),
        opos)

def pc.fin(e: F.ES) -> A():
  match e:
    case F.ES{tok, l, w, k, nt, +bits, pb, go}:
      pc.out(bits, F.flush(w))

def pc.a(+lens: List<&2, U32>, r: F.R2) -> A():
  match r:
    case F.R2{c2, +nt, +n}:
      +end = (TOK() + nt : U32)
      pc.fin(pc.passb(F.es.loop(U32.to_nat(nt), F.ES{c2, F.canon(lens, F.tables()),
        F.W{Array.new(U32, Nat.max(10n, 1n+F.depth(32n, 1n, (n + 8 : U32))), 0), 0, 0, 8},
        TOK(), end, 0, False{}, F.lt(TOK(), end)})))

# A strip's tokens (from phase A) in; its record out: payload bytes,
# symbol bits, payload.
def phase_c(c: A(), +lens: List<&2, U32>) -> A():
  pc.a(lens, F.get2(c, 320, 321))

# ------------------------------------------------ decoding a strip

def dd.b(+rb: U32, +bpp: U32, pr: A() & U32) -> A():
  (f, +cnt) = pr
  +rows = (cnt / (rb + 1 : U32) : U32)
  P.unfilter(f, 0, rows, rb, bpp)

def dd.a(+lens: List<&2, U32>, +cnt: U32, +rb: U32, +bpp: U32, s: F.SL) -> A():
  match s:
    case F.SL{wv, +h}:
      +nbits = F.be32(List.drop(&2, U32, F.tops(h), 4n))
      +end = (64 + nbits : U32)
      +dep = Nat.max(10n, 2n+F.depth(32n, 1n, cnt))
      dd.b(rb, bpp, F.arr_len(F.da.fin(F.ds.loop(U32.to_nat(nbits), F.DS{wv,
        F.dtable(lens), Array.new(U32, dep, 0), U32.pow(2, dep), 64, end, 0,
        end, F.lt(64, end)}))))

def dd.w(+lens: List<&2, U32>, +rb: U32, +bpp: U32, pr: A() & U32) -> A():
  (r, +cnt) = pr
  dd.a(lens, cnt, rb, bpp, F.slice(F.win(r, cnt), 0, 8))

# A strip's record in; its pixels out.
def phase_d(r: A(), +lens: List<&2, U32>, +rb: U32, +bpp: U32) -> A():
  dd.w(lens, rb, bpp, F.arr_len(r))

# ------------------------------------------------ the three parallel maps
# Each has a sequential twin; LAWS.bend states that the two agree.

def map_a(t: T.AT, +rb: U32, +bpp: U32, +none: Bool) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_a(a, rb, bpp, none)}
    case T.ANd{lo, hi}:
      x y = map_a(lo, rb, bpp, none) map_a(hi, rb, bpp, none)
      T.ANd{x, y}

def map_a_seq(t: T.AT, +rb: U32, +bpp: U32, +none: Bool) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_a(a, rb, bpp, none)}
    case T.ANd{lo, hi}:
      T.ANd{map_a_seq(lo, rb, bpp, none), map_a_seq(hi, rb, bpp, none)}

def map_c(t: T.AT, +lens: List<&2, U32>) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_c(a, lens)}
    case T.ANd{lo, hi}:
      x y = map_c(lo, lens) map_c(hi, lens)
      T.ANd{x, y}

def map_c_seq(t: T.AT, +lens: List<&2, U32>) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_c(a, lens)}
    case T.ANd{lo, hi}:
      T.ANd{map_c_seq(lo, lens), map_c_seq(hi, lens)}

def map_d(t: T.AT, +lens: List<&2, U32>, +rb: U32, +bpp: U32) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_d(a, lens, rb, bpp)}
    case T.ANd{lo, hi}:
      x y = map_d(lo, lens, rb, bpp) map_d(hi, lens, rb, bpp)
      T.ANd{x, y}

def map_d_seq(t: T.AT, +lens: List<&2, U32>, +rb: U32, +bpp: U32) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_d(a, lens, rb, bpp)}
    case T.ANd{lo, hi}:
      T.ANd{map_d_seq(lo, lens, rb, bpp), map_d_seq(hi, lens, rb, bpp)}

def pick_a(par: Bool, t: T.AT, +rb: U32, +bpp: U32, +none: Bool) -> T.AT:
  match par:
    case True{}:
      map_a(t, rb, bpp, none)
    case False{}:
      map_a_seq(t, rb, bpp, none)

def pick_c(par: Bool, t: T.AT, +lens: List<&2, U32>) -> T.AT:
  match par:
    case True{}:
      map_c(t, lens)
    case False{}:
      map_c_seq(t, lens)

def pick_d(par: Bool, t: T.AT, +lens: List<&2, U32>, +rb: U32, +bpp: U32) -> T.AT:
  match par:
    case True{}:
      map_d(t, lens, rb, bpp)
    case False{}:
      map_d_seq(t, lens, rb, bpp)

# ------------------------------------------------ encode and decode

def MINSTRIP() -> U32:
  65536

def header(+w: U32, +h: U32, +rps: U32, +ch: U32, +bps: U32, +pch: U32,
  +lens: List<&2, U32>) -> A():
  F.of_list(Con{66, Con{90, Con{73, Con{49, F.u32be(w, F.u32be(h, F.u32be(rps,
    Con{ch, Con{bps, Con{pch, Con{0, lens}}}})))}}}})

def pal_bytes(pal: List<&2, U32>) -> List<&2, U32>:
  match pal:
    case Nil{}:
      Nil{}
    case Con{+e, r}:
      Con{(e .&. 255 : U32), Con{((e >> 8n : U32) .&. 255 : U32),
        Con{((e >> 16n : U32) .&. 255 : U32), Con{(e >> 24n : U32), pal_bytes(r)}}}}

def with_pal(indexed: Bool, +pal: List<&2, U32>, xs: List<&1, A()>) -> List<&1, A()>:
  match indexed:
    case False{}:
      xs
    case True{}:
      Con{F.of_list(F.u32be(1024, F.u32be(0, pal_bytes(pal)))), xs}

def en.c(+w: U32, +h: U32, +rps: U32, +ch: U32, +bps: U32, +pal: List<&2, U32>,
  +pch: U32, +par: Bool, s: GS) -> List<&1, A()>:
  match s:
    case GS{g, kept}:
      +lens = F.lengths(F.to_list(g, 320))
      Con{header(w, h, rps, ch, bps, pch, lens), with_pal(F.lt(0, pch), pal,
        T.leaves(pick_c(par, T.collapse(40n,
          T.wrap(List.reverse(&1, Array<U32>, kept))), lens), Nil{}))}

# An image in; the .bzi file out, as a header and one record per strip.
def encode(im: P.IM, +par: Bool) -> List<&1, A()>:
  match im:
    case P.IM{px, +w, +h, +ch, +bps, ok, +pal, +pch}:
      +bpp = (ch * bps : U32)
      +rb = (w * bpp : U32)
      +total = (h * rb : U32)
      +s = U32.min(256, U32.min(U32.max(1, h), U32.max(1, (total / MINSTRIP() : U32))))
      +rps = U32.max(1, (((h + s : U32) - 1 : U32) / s : U32))
      +count = U32.max(1, (((h + rps : U32) - 1 : U32) / rps : U32))
      en.c(w, h, rps, ch, bps, pal, pch, par, gather(T.leaves(pick_a(par,
        T.collapse(40n, T.wrap(split(px, total, (rps * rb : U32), count))), rb, bpp,
          F.lt(0, pch)),
        Nil{}), GS{Array.new(U32, 9n, 0), Nil{}}))

def nth(xs: List<&2, U32>, n: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, xs, n), 0)

# a palette strip: indices decoded, then looked up (in the same task)
def phase_dp.b(+w: U32, +pal: List<&2, U32>, +pch: U32, pr: A() & U32) -> A():
  (ix, +cnt) = pr
  +rows = Bool.pick(U32, U32.is_eq(w, 0), 0, (cnt / U32.max(w, 1) : U32))
  P.expand(ix, P.pal_array(pal), w, rows, w, pch, 8)

def phase_dp(r: A(), +lens: List<&2, U32>, +w: U32, +pal: List<&2, U32>,
  +pch: U32) -> A():
  phase_dp.b(w, pal, pch, F.arr_len(phase_d(r, lens, w, 1)))

def map_dp(t: T.AT, +lens: List<&2, U32>, +w: U32, +pal: List<&2, U32>,
  +pch: U32) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_dp(a, lens, w, pal, pch)}
    case T.ANd{lo, hi}:
      x y = map_dp(lo, lens, w, pal, pch) map_dp(hi, lens, w, pal, pch)
      T.ANd{x, y}

def map_dp_seq(t: T.AT, +lens: List<&2, U32>, +w: U32, +pal: List<&2, U32>,
  +pch: U32) -> T.AT:
  match t:
    case T.ALf{a}:
      T.ALf{phase_dp(a, lens, w, pal, pch)}
    case T.ANd{lo, hi}:
      T.ANd{map_dp_seq(lo, lens, w, pal, pch), map_dp_seq(hi, lens, w, pal, pch)}

def pick_dp(par: Bool, t: T.AT, +lens: List<&2, U32>, +w: U32,
  +pal: List<&2, U32>, +pch: U32) -> T.AT:
  match par:
    case True{}:
      map_dp(t, lens, w, pal, pch)
    case False{}:
      map_dp_seq(t, lens, w, pal, pch)

def words(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+a, r1}:
      match r1:
        case Nil{}:
          Nil{}
        case Con{+b, r2}:
          match r2:
            case Nil{}:
              Nil{}
            case Con{+c, r3}:
              match r3:
                case Nil{}:
                  Nil{}
                case Con{+d, r4}:
                  Con{(a .|. (b << 8n) .|. (c << 16n) .|. (d << 24n) : U32), words(r4)}

def de.pal(recs: List<&1, A()>, +w: U32, +h: U32, +lens: List<&2, U32>,
  +pch: U32, par: Bool) -> List<&1, A()>:
  match recs:
    case Nil{}:
      Nil{}
    case Con{pr, rest}:
      Con{F.of_list(P.pam_header(w, h, pch, 1)), T.leaves(pick_dp(par,
        T.collapse(40n, T.wrap(rest)), lens, w,
        words(List.drop(&2, U32, F.bytes_list(pr, 1032), 8n)), pch), Nil{})}

def de.plain(recs: List<&1, A()>, +w: U32, +h: U32, +ch: U32, +bps: U32,
  +lens: List<&2, U32>, par: Bool) -> List<&1, A()>:
  +bpp = (ch * bps : U32)
  Con{F.of_list(P.pam_header(w, h, ch, bps)), T.leaves(pick_d(par,
    T.collapse(40n, T.wrap(recs)), lens, (w * bpp : U32), bpp), Nil{})}

def de.sel(indexed: Bool, recs: List<&1, A()>, +w: U32, +h: U32, +ch: U32,
  +bps: U32, +pch: U32, +lens: List<&2, U32>, par: Bool) -> List<&1, A()>:
  match indexed:
    case True{}:
      de.pal(recs, w, h, lens, pch, par)
    case False{}:
      de.plain(recs, w, h, ch, bps, lens, par)

def de.b(recs: List<&1, A()>, +hd: List<&2, U32>, par: Bool) -> List<&1, A()>:
  +pch = nth(hd, 18n)
  de.sel(F.lt(0, pch), recs, F.be32(List.drop(&2, U32, hd, 4n)),
    F.be32(List.drop(&2, U32, hd, 8n)), nth(hd, 16n), nth(hd, 17n), pch,
    List.take(&2, U32, List.drop(&2, U32, hd, 20n), 320n), par)

# A .bzi file (header, then records) in; a PAM file out, as its header
# and one array of pixels per strip.
def decode(xs: List<&1, A()>, par: Bool) -> List<&1, A()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{hdr, recs}:
      de.b(recs, F.bytes_list(hdr, HDR()), par)

# ------------------------------------------------ for stating claims

def bytes_of.one(pr: A() & U32) -> List<&2, U32>:
  (a, +n) = pr
  F.bytes_list(a, n)

# every array's bytes, in order
def bytes_of(xs: List<&1, A()>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, r}:
      List.append(&2, U32, bytes_of.one(F.arr_len(a)), bytes_of(r))

# the image as a PAM file: header, then its (true-colour) pixels
def pam.b(im: P.IM) -> List<&1, A()>:
  match im:
    case P.IM{px, +w, +h, +ch, +bps, ok, pal, pch}:
      [F.of_list(P.pam_header(w, h, ch, bps)), px]

def pam(im: P.IM) -> List<&1, A()>:
  pam.b(P.to_rgb(im))
