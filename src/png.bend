import Base
import ./fast.bend as F
import ./inflate.bend as I

# ======================================================================
# PNG decoding (non-interlaced; all colour types and bit depths).
#
# Arrays are packed chunk arrays (four bytes per slot, little-endian,
# byte count in the last slot). The result is a canonical image: its
# rows back to back, `ch` channels of `bps` bytes each (16-bit samples
# big-endian, as in PNG). Palette images become RGB, or RGBA when tRNS
# gives alpha; 1/2/4-bit grey is scaled to 8 bits.
# ======================================================================

def A() -> Type:
  Array<U32>

# ------------------------------------------------ bytes of a packed array

def rd8.b(+i: U32, pr: A() & U32) -> A() & U32:
  (a, +w) = pr
  (a, F.byte_of(w, i))

def rd8(a: A(), +i: U32) -> A() & U32:
  rd8.b(i, F.get(a, (i >> 2n : U32)))

def be.d(+x: U32, pr: A() & U32) -> A() & U32:
  (a, +b) = pr
  (a, ((x << 8n : U32) .|. b : U32))

def be.c(+i: U32, pr: A() & U32) -> A() & U32:
  (a, +x) = pr
  be.d(x, rd8(a, (i + 3 : U32)))

def be.b(+i: U32, pr: A() & U32) -> A() & U32:
  (a, +x) = pr
  be.c(i, be.d(x, rd8(a, (i + 2 : U32))))

def be.a(+i: U32, pr: A() & U32) -> A() & U32:
  (a, +x) = pr
  be.b(i, be.d(x, rd8(a, (i + 1 : U32))))

# the big-endian u32 at byte i
def be32(a: A(), +i: U32) -> A() & U32:
  be.a(i, rd8(a, i))

# ------------------------------------------------ the chunk walk
# IHDR is always first, at fixed offsets. The walk collects PLTE, tRNS
# and the IDAT segments (as offset, length pairs, newest first).

type PW is Type:
  PW{f: Array<U32>, o: U32, n: U32, plo: U32, pln: U32, tro: U32, trn: U32,
    idat: List<&2, U32>, go: Bool}

def IDAT() -> U32:
  1229209940

def PLTE() -> U32:
  1347179589

def TRNS() -> U32:
  1951551059

def IEND() -> U32:
  1229278788

def pw.c(+o: U32, +n: U32, +plo: U32, +pln: U32, +tro: U32, +trn: U32,
  +idat: List<&2, U32>, +len: U32, pr: A() & U32) -> PW:
  (f, +t) = pr
  +d = (o + 8 : U32)
  +o2 = (o + 12 + len : U32)
  +isp = U32.is_eq(t, PLTE())
  +ist = U32.is_eq(t, TRNS())
  PW{f, o2, n, Bool.pick(U32, isp, d, plo), Bool.pick(U32, isp, len, pln),
    Bool.pick(U32, ist, d, tro), Bool.pick(U32, ist, len, trn),
    Bool.pick(List<&2, U32>, U32.is_eq(t, IDAT()), Con{d, Con{len, idat}}, idat),
    Bool.and(U32.is_ne(t, IEND()), U32.is_le((o2 + 12 : U32), n))}

def pw.b(+o: U32, +n: U32, +plo: U32, +pln: U32, +tro: U32, +trn: U32,
  +idat: List<&2, U32>, pr: A() & U32) -> PW:
  (f, +len) = pr
  pw.c(o, n, plo, pln, tro, trn, idat, len, be32(f, (o + 4 : U32)))

def pw.loop(f: Nat, s: PW) -> PW:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case PW{fa, +o, +n, +plo, +pln, +tro, +trn, +idat, go}:
          match go:
            case False{}:
              PW{fa, o, n, plo, pln, tro, trn, idat, False{}}
            case True{}:
              pw.loop(g, pw.b(o, n, plo, pln, tro, trn, idat, be32(fa, o)))

# ------------------------------------------------ joining the IDAT data

type JC is Type:
  JC{f: Array<U32>, z: Array<U32>, q: U32, zpos: U32}

def jc.b(z: A(), +q: U32, +zpos: U32, pr: A() & U32) -> JC:
  (f, +b) = pr
  JC{f, F.set_byte(z, zpos, b), (q + 1 : U32), (zpos + 1 : U32)}

def jc.loop(f: Nat, s: JC) -> JC:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case JC{fa, z, +q, +zpos}:
          jc.loop(g, jc.b(z, q, zpos, rd8(fa, q)))

def join.at(+o: U32, +len: U32, s: JC) -> JC:
  match s:
    case JC{f, z, q, zpos}:
      jc.loop(U32.to_nat(len), JC{f, z, o, zpos})

# segments are listed newest first; join them oldest first
def join(xs: List<&2, U32>, s: JC) -> JC:
  match xs:
    case Nil{}:
      s
    case Con{+o, r1}:
      match r1:
        case Nil{}:
          s
        case Con{+len, r2}:
          join.at(o, len, join(r2, s))

def seglen(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{o, r1}:
      match r1:
        case Nil{}:
          acc
        case Con{+len, r2}:
          seglen(r2, (acc + len : U32))

# ------------------------------------------------ unfiltering
# `rows` scanlines of `rb` bytes, each preceded by a filter type byte,
# starting at byte `q` of `src`; `bpp` is the filter's byte stride. The
# neighbours are always read (outside the image they read garbage) and
# then masked to 0, so every byte is one uniform step.

def absd(+x: U32, +y: U32) -> U32:
  Bool.pick(U32, U32.is_le(y, x), (x - y : U32), (y - x : U32))

def pred(+t: U32, +a: U32, +b: U32, +c: U32) -> U32:
  +pa = absd(b, c)
  +pb = absd(a, c)
  +pc = absd((a + b : U32), (c + c : U32))
  +paeth = Bool.pick(U32, Bool.and(U32.is_le(pa, pb), U32.is_le(pa, pc)), a,
    Bool.pick(U32, U32.is_le(pb, pc), b, c))
  Bool.pick(U32, U32.is_eq(t, 0), 0, Bool.pick(U32, U32.is_eq(t, 1), a,
    Bool.pick(U32, U32.is_eq(t, 2), b, Bool.pick(U32, U32.is_eq(t, 3),
      ((a + b : U32) >> 1n : U32), paeth))))

type UB is Type:
  UB{src: Array<U32>, out: Array<U32>, q: U32, opos: U32, col: U32}

def ub.d(src: A(), +q: U32, +opos: U32, +col: U32, +t: U32, +up: Bool,
  +left: Bool, +x: U32, +a: U32, +b: U32, pr: A() & U32) -> UB:
  (out, +c) = pr
  +a1 = Bool.pick(U32, left, a, 0)
  +b1 = Bool.pick(U32, up, b, 0)
  +c1 = Bool.pick(U32, Bool.and(left, up), c, 0)
  UB{src, F.set_byte(out, opos, ((x + pred(t, a1, b1, c1) : U32) .&. 255 : U32)),
    (q + 1 : U32), (opos + 1 : U32), (col + 1 : U32)}

def ub.c(src: A(), +q: U32, +opos: U32, +col: U32, +t: U32, +up: Bool,
  +left: Bool, +rb: U32, +bpp: U32, +x: U32, +a: U32, pr: A() & U32) -> UB:
  (out, +b) = pr
  ub.d(src, q, opos, col, t, up, left, x, a, b,
    rd8(out, (opos - rb - bpp : U32)))

def ub.b(src: A(), +q: U32, +opos: U32, +col: U32, +t: U32, +up: Bool,
  +rb: U32, +bpp: U32, +x: U32, pr: A() & U32) -> UB:
  (out, +a) = pr
  ub.c(src, q, opos, col, t, up, U32.is_le(bpp, col), rb, bpp, x, a,
    rd8(out, (opos - rb : U32)))

def ub.a(out: A(), +q: U32, +opos: U32, +col: U32, +t: U32, +up: Bool,
  +rb: U32, +bpp: U32, pr: A() & U32) -> UB:
  (src, +x) = pr
  ub.b(src, q, opos, col, t, up, rb, bpp, x, rd8(out, (opos - bpp : U32)))

def ub.loop(f: Nat, +t: U32, +up: Bool, +rb: U32, +bpp: U32, s: UB) -> UB:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case UB{src, out, +q, +opos, +col}:
          ub.loop(g, t, up, rb, bpp, ub.a(out, q, opos, col, t, up, rb, bpp,
            rd8(src, q)))

def ur.b(+row: U32, +rb: U32, +bpp: U32, +q: U32, out: A(), +opos: U32,
  pr: A() & U32) -> UB:
  (src, +t) = pr
  ub.loop(U32.to_nat(rb), t, F.lt(0, row), rb, bpp,
    UB{src, out, (q + 1 : U32), opos, 0})

type UR is Type:
  UR{src: Array<U32>, out: Array<U32>, q: U32, opos: U32, row: U32}

def ur.c(+row: U32, s: UB) -> UR:
  match s:
    case UB{src, out, +q, +opos, col}:
      UR{src, out, q, opos, (row + 1 : U32)}

def ur.loop(f: Nat, +rb: U32, +bpp: U32, s: UR) -> UR:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case UR{src, out, +q, +opos, +row}:
          ur.loop(g, rb, bpp, ur.c(row, ur.b(row, rb, bpp, q, out, opos,
            rd8(src, q))))

def ur.fin(+len: U32, s: UR) -> A():
  match s:
    case UR{src, out, q, opos, row}:
      F.pack_cap(out, len)

# Unfilter `rows` scanlines of `rb` bytes starting at byte `q` of `src`:
# the result holds rows * rb bytes, packed, count in the last slot.
def unfilter(src: A(), +q: U32, +rows: U32, +rb: U32, +bpp: U32) -> A():
  +len = (rows * rb : U32)
  ur.fin(len, ur.loop(U32.to_nat(rows), rb, bpp,
    UR{src, F.new_packed(len), q, 0, 0}))

# ------------------------------------------------ palettes and small depths
# Both palette images and 1/2/4-bit grey go through a 256-entry lookup:
# entry v is the pixel for sample v, packed r | g << 8 | b << 16 | a << 24
# (grey uses only the low byte).

type PB is Type:
  PB{f: Array<U32>, pal: Array<U32>, i: U32}

def pb.d(pal: A(), +i: U32, +pln: U32, +trn: U32, +r: U32, +g: U32, +b: U32,
  pr: A() & U32) -> PB:
  (f, +a) = pr
  +has = U32.is_le(((i * 3 : U32) + 3 : U32), pln)
  +rgb = Bool.pick(U32, has,
    (r .|. (g << 8n : U32) .|. (b << 16n : U32) : U32), 0)
  +alpha = Bool.pick(U32, F.lt(i, trn), a, 255)
  PB{f, Array.set(U32, pal, i, (rgb .|. (alpha << 24n : U32) : U32)), (i + 1 : U32)}

def pb.c(pal: A(), +i: U32, +plo: U32, +pln: U32, +tro: U32, +trn: U32,
  +r: U32, +g: U32, pr: A() & U32) -> PB:
  (f, +b) = pr
  pb.d(pal, i, pln, trn, r, g, b, rd8(f, (tro + i : U32)))

def pb.b(pal: A(), +i: U32, +plo: U32, +pln: U32, +tro: U32, +trn: U32,
  +r: U32, pr: A() & U32) -> PB:
  (f, +g) = pr
  pb.c(pal, i, plo, pln, tro, trn, r, g, rd8(f, (plo + (i * 3 : U32) + 2 : U32)))

def pb.a(pal: A(), +i: U32, +plo: U32, +pln: U32, +tro: U32, +trn: U32,
  pr: A() & U32) -> PB:
  (f, +r) = pr
  pb.b(pal, i, plo, pln, tro, trn, r, rd8(f, (plo + (i * 3 : U32) + 1 : U32)))

def pb.loop(f: Nat, +plo: U32, +pln: U32, +tro: U32, +trn: U32, s: PB) -> PB:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case PB{fa, pal, +i}:
          pb.loop(g, plo, pln, tro, trn, pb.a(pal, i, plo, pln, tro, trn,
            rd8(fa, (plo + (i * 3 : U32) : U32))))

def grey.loop(f: Nat, +i: U32, +scale: U32, pal: A()) -> A():
  match f:
    case 0n:
      pal
    case 1n+g:
      grey.loop(g, (i + 1 : U32), scale, Array.set(U32, pal, i, (i * scale : U32)))

# ------------------------------------------------ expanding samples

# replace byte `i` (not OR: neighbouring pixels share slots)
def put8.b(+i: U32, +v: U32, pr: A() & U32) -> A():
  (a, +w) = pr
  +s = ((i .&. 3 : U32) << 3n : U32)
  Array.set(U32, a, (i >> 2n : U32),
    ((w .&. U32.not(F.shl(255, s)) : U32) .|. F.shl((v .&. 255 : U32), s) : U32))

def put8(a: A(), +i: U32, +v: U32) -> A():
  put8.b(i, v, F.get(a, (i >> 2n : U32)))

# the low `k` bytes of e, at bytes opos..opos+k-1
def putn(f: Nat, +opos: U32, +e: U32, out: A()) -> A():
  match f:
    case 0n:
      out
    case 1n+g:
      putn(g, (opos + 1 : U32), (e >> 8n : U32), put8(out, opos, e))

type CV is Type:
  CV{rows: Array<U32>, pal: Array<U32>, out: Array<U32>, x: U32, y: U32,
    opos: U32}

def cv.c(rows: A(), out: A(), +x: U32, +y: U32, +opos: U32, +w: U32,
  +ch: U32, pr: A() & U32) -> CV:
  (pal, +e) = pr
  +x1 = (x + 1 : U32)
  +wrap = U32.is_eq(x1, w)
  CV{rows, pal, putn(U32.to_nat(ch), opos, e, out), Bool.pick(U32, wrap, 0, x1),
    Bool.pick(U32, wrap, (y + 1 : U32), y), (opos + ch : U32)}

def cv.b(pal: A(), out: A(), +x: U32, +y: U32, +opos: U32, +w: U32,
  +ch: U32, +d: U32, +bit: U32, pr: A() & U32) -> CV:
  (rows, +byte) = pr
  +v = (F.shr(byte, (8 - d - (bit .&. 7 : U32) : U32)) .&. I.mask(d) : U32)
  cv.c(rows, out, x, y, opos, w, ch, F.get(pal, v))

def cv.loop(f: Nat, +w: U32, +rb: U32, +ch: U32, +d: U32, s: CV) -> CV:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CV{rows, pal, out, +x, +y, +opos}:
          +bit = (x * d : U32)
          cv.loop(g, w, rb, ch, d, cv.b(pal, out, x, y, opos, w, ch, d, bit,
            rd8(rows, ((y * rb : U32) + (bit >> 3n : U32) : U32))))

def cv.fin(+len: U32, s: CV) -> A():
  match s:
    case CV{rows, pal, out, x, y, opos}:
      F.pack_cap(out, len)

# rows of samples (d bits each) through the lookup, ch bytes per pixel
def expand(rows: A(), pal: A(), +w: U32, +h: U32, +rb: U32, +ch: U32, +d: U32) -> A():
  +len = (w * h * ch : U32)
  cv.fin(len, cv.loop(U32.to_nat((w * h : U32)), w, rb, ch, d,
    CV{rows, pal, F.new_packed(len), 0, 0, 0}))

# ------------------------------------------------ decoding

# A decoded image: rows back to back, ch channels of bps bytes. A palette
# image keeps its indices (ch = bps = 1) with `pal` its 256 entries
# (r | g << 8 | b << 16 | a << 24) and `pch` its channels once expanded
# (3, or 4 with tRNS); `pch` is 0 for every other image.
type IM is Type:
  IM{px: Array<U32>, w: U32, h: U32, ch: U32, bps: U32, ok: Bool,
    pal: List<&2, U32>, pch: U32}

def rawch(+ct: U32) -> U32:
  Bool.pick(U32, U32.is_eq(ct, 2), 3, Bool.pick(U32, U32.is_eq(ct, 4), 2,
    Bool.pick(U32, U32.is_eq(ct, 6), 4, 1)))

def valid(+ct: U32, +d: U32, +il: U32, +sig: U32) -> Bool:
  +big = Bool.or(U32.is_eq(d, 8), U32.is_eq(d, 16))
  +small = Bool.or(U32.is_eq(d, 1), Bool.or(U32.is_eq(d, 2), U32.is_eq(d, 4)))
  Bool.and(Bool.and(U32.is_eq(il, 0), U32.is_eq(sig, 2303741511)),
    Bool.pick(Bool, U32.is_eq(ct, 0), Bool.or(big, small),
      Bool.pick(Bool, U32.is_eq(ct, 3), Bool.or(small, U32.is_eq(d, 8)),
        Bool.pick(Bool, Bool.or(U32.is_eq(ct, 2), Bool.or(U32.is_eq(ct, 4),
          U32.is_eq(ct, 6))), big, False{}))))

# palette images keep their indices, one byte each
def conv.pal(rows: A(), +w: U32, +h: U32, +rb: U32, +ch: U32, +d: U32,
  +ok: Bool, s: PB) -> IM:
  match s:
    case PB{f, pal, i}:
      IM{expand(rows, grey.loop(256n, 0, 1, Array.new(U32, 8n, 0)), w, h, rb, 1, d),
        w, h, 1, 1, ok, F.to_list(pal, 256), ch}

# three ways from unfiltered rows to canonical pixels
def conv(direct: Bool, palette: Bool, f: A(), rows: A(), +w: U32, +h: U32,
  +rb: U32, +ct: U32, +d: U32, +plo: U32, +pln: U32, +tro: U32, +trn: U32,
  +ok: Bool) -> IM:
  match direct:
    case True{}:
      IM{rows, w, h, rawch(ct), (d >> 3n : U32), ok, Nil{}, 0}
    case False{}:
      match palette:
        case True{}:
          +ch = Bool.pick(U32, F.lt(0, trn), 4, 3)
          conv.pal(rows, w, h, rb, ch, d, ok,
            pb.loop(256n, plo, pln, tro, trn, PB{f, Array.new(U32, 8n, 0), 0}))
        case False{}:
          IM{expand(rows, grey.loop(256n, 0, (255 / I.mask(d) : U32),
            Array.new(U32, 8n, 0)), w, h, rb, 1, d), w, h, 1, 1, ok, Nil{}, 0}

def dec.z(f: A(), z: A(), +w: U32, +h: U32, +d: U32, +ct: U32, +ok: Bool,
  +plo: U32, +pln: U32, +tro: U32, +trn: U32) -> IM:
  +bpx = (rawch(ct) * d : U32)
  +rb = (((w * bpx : U32) + 7 : U32) >> 3n : U32)
  rows = unfilter(I.inflate(z, 16, (h * (rb + 1 : U32) : U32)), 0, h, rb,
    U32.max(1, (bpx >> 3n : U32)))
  conv(Bool.and(U32.is_ne(ct, 3), U32.is_le(8, d)), U32.is_eq(ct, 3), f, rows,
    w, h, rb, ct, d, plo, pln, tro, trn, ok)

def dec.j(+w: U32, +h: U32, +d: U32, +ct: U32, +ok: Bool, +plo: U32, +pln: U32,
  +tro: U32, +trn: U32, s: JC) -> IM:
  match s:
    case JC{f, z, q, zpos}:
      dec.z(f, z, w, h, d, ct, ok, plo, pln, tro, trn)

def dec.w(+w: U32, +h: U32, +d: U32, +ct: U32, +ok: Bool, s: PW) -> IM:
  match s:
    case PW{f, o, n, +plo, +pln, +tro, +trn, +idat, go}:
      dec.j(w, h, d, ct, ok, plo, pln, tro, trn,
        join(idat, JC{f, F.new_packed(seglen(idat, 0)), 0, 0}))

def dec.e(+n: U32, +w: U32, +h: U32, +d: U32, +ct: U32, +sig: U32,
  pr: A() & U32) -> IM:
  (f, +il) = pr
  +ok = valid(ct, d, il, sig)
  dec.w(Bool.pick(U32, ok, w, 0), Bool.pick(U32, ok, h, 0), d, ct, ok,
    pw.loop(U32.to_nat(((n / 12 : U32) + 2 : U32)),
      PW{f, 8, n, 0, 0, 0, 0, Nil{}, True{}}))

def dec.d(+n: U32, +w: U32, +h: U32, +d: U32, +sig: U32, pr: A() & U32) -> IM:
  (f, +ct) = pr
  dec.e(n, w, h, d, ct, sig, rd8(f, 28))

def dec.c(+n: U32, +w: U32, +h: U32, +sig: U32, pr: A() & U32) -> IM:
  (f, +d) = pr
  dec.d(n, w, h, d, sig, rd8(f, 25))

def dec.b(+n: U32, +w: U32, +sig: U32, pr: A() & U32) -> IM:
  (f, +h) = pr
  dec.c(n, w, h, sig, rd8(f, 24))

def dec.a(+n: U32, +sig: U32, pr: A() & U32) -> IM:
  (f, +w) = pr
  dec.b(n, w, sig, be32(f, 20))

def dec.s(+n: U32, pr: A() & U32) -> IM:
  (f, +sig) = pr
  dec.a(n, sig, be32(f, 16))

# Decode a PNG file of n bytes (a packed array). `ok` is False for what
# this decoder does not handle (interlaced images, bad headers); the size
# is then 0 x 0 so nothing is decoded.
def decode(f: A(), +n: U32) -> IM:
  dec.s(n, be32(f, 0))

# ------------------------------------------------ PAM output

def str_bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Con{x, str_bytes(t)}

def tupltype(+ch: U32) -> String:
  Bool.pick(String, U32.is_eq(ch, 1), "GRAYSCALE", Bool.pick(String,
    U32.is_eq(ch, 2), "GRAYSCALE_ALPHA", Bool.pick(String, U32.is_eq(ch, 3),
      "RGB", "RGB_ALPHA")))

def ushow(+x: U32) -> String:
  U32.show(x)

# the header of a PAM (Netpbm) file holding such an image
def pam_header(+w: U32, +h: U32, +ch: U32, +bps: U32) -> List<&2, U32>:
  str_bytes("P7\nWIDTH " ++ ushow(w) ++ "\nHEIGHT " ++ ushow(h) ++ "\nDEPTH " ++
    ushow(ch) ++ "\nMAXVAL " ++ Bool.pick(String, U32.is_eq(bps, 2), "65535", "255") ++
    "\nTUPLTYPE " ++ tupltype(ch) ++ "\nENDHDR\n")

# ------------------------------------------------ palette expansion

def pal_array(pal: List<&2, U32>) -> A():
  F.put_list(pal, 0, Array.new(U32, 8n, 0))

def rgb.sel(indexed: Bool, px: A(), +w: U32, +h: U32, +ch: U32, +bps: U32,
  +ok: Bool, +pal: List<&2, U32>, +pch: U32) -> IM:
  match indexed:
    case False{}:
      IM{px, w, h, ch, bps, ok, pal, pch}
    case True{}:
      IM{expand(px, pal_array(pal), w, h, w, pch, 8), w, h, pch, 1, ok, Nil{}, 0}

# The image with any palette applied: true colour, as PAM wants it.
def to_rgb(im: IM) -> IM:
  match im:
    case IM{px, +w, +h, +ch, +bps, +ok, +pal, +pch}:
      rgb.sel(F.lt(0, pch), px, w, h, ch, bps, ok, pal, pch)
