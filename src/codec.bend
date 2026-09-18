import Base
import ./byte.bend as B
import ./bits.bend as Bits
import ./tab.bend as Tab
import ./huff.bend as Huff
import ./lz.bend as LZ
import ./chunks.bend as Chunks

# --------------------------------------------------- the code tables

# Deflate's length and distance codes: a base value plus a field of
# extra bits. Literals are symbols with `hi = False`; a length code and
# a distance code are symbols with `hi = True` and `lo` the table index
# (lengths at 0.., distances at 29..). Because a length code is always
# followed by a distance code, the decoder never has to ask which kind
# of symbol it is holding -- the shape of the stream says so.
type Ent is Data:
  Ent{base: Nat, xb: Nat}

# Big Nat literals expand to unary at check time, so anything past a
# couple of dozen is built from a machine word instead.
def nn(w: U32) -> Nat:
  U32.to_nat(w)

def DBIAS() -> Nat:
  29n

def MAXDIST() -> Nat:
  nn(32768)

def len_tab() -> List<&2, Ent>:
  [Ent{3n, 0n}, Ent{4n, 0n}, Ent{5n, 0n}, Ent{6n, 0n}, Ent{7n, 0n},
   Ent{8n, 0n}, Ent{9n, 0n}, Ent{10n, 0n}, Ent{11n, 1n}, Ent{13n, 1n},
   Ent{15n, 1n}, Ent{17n, 1n}, Ent{19n, 2n}, Ent{23n, 2n}, Ent{27n, 2n},
   Ent{31n, 2n}, Ent{35n, 3n}, Ent{43n, 3n}, Ent{51n, 3n}, Ent{59n, 3n},
   Ent{67n, 4n}, Ent{83n, 4n}, Ent{99n, 4n}, Ent{nn(115), 4n}, Ent{nn(131), 5n},
   Ent{nn(163), 5n}, Ent{nn(195), 5n}, Ent{nn(227), 5n}, Ent{nn(258), 0n}]

def dist_tab() -> List<&2, Ent>:
  [Ent{1n, 0n}, Ent{2n, 0n}, Ent{3n, 0n}, Ent{4n, 0n}, Ent{5n, 1n},
   Ent{7n, 1n}, Ent{9n, 2n}, Ent{13n, 2n}, Ent{17n, 3n}, Ent{25n, 3n},
   Ent{33n, 4n}, Ent{49n, 4n}, Ent{65n, 5n}, Ent{97n, 5n}, Ent{nn(129), 6n},
   Ent{nn(193), 6n}, Ent{nn(257), 7n}, Ent{nn(385), 7n}, Ent{nn(513), 8n},
   Ent{nn(769), 8n}, Ent{nn(1025), 9n}, Ent{nn(1537), 9n}, Ent{nn(2049), 10n},
   Ent{nn(3073), 10n}, Ent{nn(4097), 11n}, Ent{nn(6145), 11n}, Ent{nn(8193), 12n},
   Ent{nn(12289), 12n}, Ent{nn(16385), 13n}, Ent{nn(24577), 13n}]

def e_base(e: Ent) -> Nat:
  match e:
    case Ent{b, x}:
      b

def e_xb(e: Ent) -> Nat:
  match e:
    case Ent{b, x}:
      x

def le_base(e: Ent, +v: Nat) -> Bool:
  match e:
    case Ent{b, x}:
      Nat.is_le(b, v)

# The last entry whose base still fits: the table is ascending, and the
# scan is unconditional so it needs no branch in a recursive position.
def scan(t: List<&2, Ent>, +v: Nat, +i: Nat, best: Nat) -> Nat:
  match t:
    case Nil{}:
      best
    case Con{e, r}:
      scan(r, v, 1n+i, Bool.pick(Nat, le_base(e, v), i, best))

def ent_at(t: List<&2, Ent>, i: Nat) -> Ent:
  Maybe.default(&2, Ent, List.get(&2, Ent, t, i), Ent{0n, 0n})

def len_idx(v: Nat) -> Nat:
  scan(len_tab(), v, 0n, 0n)

def dist_idx(v: Nat) -> Nat:
  scan(dist_tab(), v, 0n, 0n)

def bv(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def bits_val(w: Nat, p: B.Bits(), acc: Nat) -> Nat:
  match w:
    case 0n:
      acc
    case 1n+k:
      match p:
        case Nil{}:
          acc
        case Con{b, r}:
          bits_val(k, r, Nat.add(Nat.mul(acc, 2n), bv(b)))

def xbits_of(+e: Ent, v: Nat) -> B.Bits():
  Huff.nat_bits(e_xb(e), Nat.sub(v, e_base(e)))

def len_xbits(+v: Nat) -> B.Bits():
  xbits_of(ent_at(len_tab(), len_idx(v)), v)

def dist_xbits(+v: Nat) -> B.Bits():
  xbits_of(ent_at(dist_tab(), dist_idx(v)), v)

def len_sym(v: Nat) -> B.Sym:
  B.Sym{True{}, B.from_u32(U32.from_nat(len_idx(v)))}

def dist_sym(v: Nat) -> B.Sym:
  B.Sym{True{}, B.from_u32(U32.from_nat(Nat.add(DBIAS(), dist_idx(v))))}

# ------------------------------------------- tokens to and from symbols

def toks_syms(ts: List<&2, LZ.Tok>) -> List<&2, B.Sym>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case LZ.Lit{b}:
          Con{B.Sym{False{}, b}, toks_syms(r)}
        case LZ.Ref{d, l}:
          Con{len_sym(l), Con{dist_sym(d), toks_syms(r)}}

def toks_xbits(ts: List<&2, LZ.Tok>) -> B.Bits():
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case LZ.Lit{b}:
          toks_xbits(r)
        case LZ.Ref{d, l}:
          List.append(&2, Bool, len_xbits(l),
            List.append(&2, Bool, dist_xbits(d), toks_xbits(r)))

def ent_of_lo(t: List<&2, Ent>, lo: B.Byte, bias: Nat) -> Ent:
  ent_at(t, Nat.sub(U32.to_nat(B.to_u32(lo)), bias))

def val_of(+e: Ent, p: B.Bits()) -> Nat:
  Nat.add(e_base(e), bits_val(e_xb(e), p, 0n))

def toks_of_syms(+ss: List<&2, B.Sym>, +p: B.Bits(),
  acc: List<&2, LZ.Tok>) -> List<&2, LZ.Tok>:
  match ss:
    case Nil{}:
      List.reverse(&2, LZ.Tok, acc)
    case Con{s, r}:
      match s:
        case B.Sym{h, lo}:
          match h:
            case False{}:
              toks_of_syms(r, p, Con{LZ.Lit{lo}, acc})
            case True{}:
              match r:
                case Nil{}:
                  List.reverse(&2, LZ.Tok, acc)
                case Con{s2, r2}:
                  match s2:
                    case B.Sym{h2, lo2}:
                      +le = ent_of_lo(len_tab(), lo, 0n)
                      +de = ent_of_lo(dist_tab(), lo2, DBIAS())
                      +p2 = List.drop(&2, Bool, p, e_xb(le))
                      toks_of_syms(r2,
                        List.drop(&2, Bool, p2, e_xb(de)),
                        Con{LZ.Ref{val_of(de, p2), val_of(le, p)}, acc})

# --------------------------------------------------- frequency counting

def count(ss: List<&2, B.Sym>, +t: Tab.Tab<&2, Nat>) -> Tab.Tab<&2, Nat>:
  match ss:
    case Nil{}:
      t
    case Con{s, r}:
      +k = B.sym_bits(s)
      count(r, Tab.set(Nat, t, k, 1n+Tab.get(Nat, t, k)))

def freqs(ss: List<&2, B.Sym>) -> List<&2, Nat>:
  Tab.list(Nat, count(ss, Tab.new(Nat, 9n, 0n)))

# --------------------------------------------------------- the container

# A chunk is: payload length (4) | symbol-section bit count (4) |
# code-length table (Huff.ALPHA bytes) | payload.
def HDR_LENS() -> Nat:
  Huff.ALPHA()

def HDR() -> Nat:
  Nat.add(8n, Huff.ALPHA())

def u32b(n: Nat) -> B.Bytes():
  +w = U32.from_nat(n)
  [B.from_u32(U32.and(U32.shrn(w, 24n), 255)),
   B.from_u32(U32.and(U32.shrn(w, 16n), 255)),
   B.from_u32(U32.and(U32.shrn(w, 8n), 255)),
   B.from_u32(U32.and(w, 255))]

def byte_at(bs: B.Bytes(), i: Nat) -> B.Byte:
  Maybe.default(&2, B.Byte, List.get(&2, B.Byte, bs, i), LZ.zero())

def b_u32_at(+bs: B.Bytes(), +i: Nat) -> Nat:
  U32.to_nat((B.to_u32(byte_at(bs, i)) * 16777216 +
    B.to_u32(byte_at(bs, 1n+i)) * 65536 +
    B.to_u32(byte_at(bs, Nat.add(i, 2n))) * 256 +
    B.to_u32(byte_at(bs, Nat.add(i, 3n))) : U32))

def magic() -> B.Bytes():
  [B.from_u32(66), B.from_u32(90), B.from_u32(55), B.from_u32(55)]

# --------------------------------------------------------- one chunk

def comp_chunk(+w: B.Bytes()) -> B.Bytes():
  +ts = LZ.parse_all(w)
  +ss = toks_syms(ts)
  +lb = Huff.build(freqs(ss))
  +sb = Huff.encode(ss, Huff.codes(Huff.canon(lb)))
  +pk = Bits.pack(List.append(&2, Bool, sb, toks_xbits(ts)))
  List.append(&2, B.Byte, u32b(List.length(&2, B.Byte, pk)),
    List.append(&2, B.Byte, u32b(List.length(&2, Bool, sb)),
      List.append(&2, B.Byte, lb, pk)))

def decomp_chunk(+blob: B.Bytes()) -> B.Bytes():
  +nbits = b_u32_at(blob, 4n)
  +lb = List.take(&2, B.Byte, List.drop(&2, B.Byte, blob, 8n), HDR_LENS())
  +bits = Bits.unpack(List.drop(&2, B.Byte, blob, HDR()))
  +tree = Huff.canon(lb)
  LZ.expand_fast_all(toks_of_syms(
    Huff.decode(List.take(&2, Bool, bits, nbits), tree, tree),
    List.drop(&2, Bool, bits, nbits), Nil{}))

def split_chunks(f: Nat, +bs: B.Bytes(),
  acc: List<&2, B.Bytes()>) -> List<&2, B.Bytes()>:
  match f:
    case 0n:
      List.reverse(&2, B.Bytes(), acc)
    case 1n+g:
      +total = {Nat.add(HDR(), b_u32_at(bs, 0n)) : Nat}
      split_chunks(g, List.drop(&2, B.Byte, bs, total),
        Con{List.take(&2, B.Byte, bs, total), acc})

def pow2(n: Nat) -> Nat:
  Nat.pow(2n, n)

# The per-chunk work as it runs inside a parallel task: octets in, octets
# out, so that converting to and from structural bytes happens on every
# core instead of once, serially, over the whole file.
def comp_oct(+ws: B.Octets()) -> B.Octets():
  B.encode(comp_chunk(B.decode(ws)))

def decomp_oct(+blob: B.Bytes()) -> B.Octets():
  B.encode(decomp_chunk(blob))

def head(+d: Nat) -> B.Octets():
  B.encode(List.append(&2, B.Byte, magic(), [B.from_u32(U32.from_nat(d))]))

# The requested depth, lowered until chunks are at least 64 KiB: every
# chunk pays a header and starts with an empty dictionary, so a small
# input split 256 ways would grow instead of shrink. The depth goes in
# the file header, so the decoder follows whatever was chosen.
def MINCHUNK() -> Nat:
  nn(65536)

def fit(+d: Nat, +n: Nat) -> Nat:
  match d:
    case 0n:
      0n
    case 1n+k:
      Bool.pick(Nat, Nat.is_le(Nat.mul(pow2(1n+k), MINCHUNK()), n), 1n+k, fit(k, n))

def compress.go(+d: Nat, +ws: B.Octets()) -> B.Octets():
  List.append(&2, U32, head(d),
    Chunks.join(U32, Chunks.pmap(~U32, ~U32, ~comp_oct, Chunks.of(U32, d, ws))))

def compress_seq.go(+d: Nat, +ws: B.Octets()) -> B.Octets():
  List.append(&2, U32, head(d),
    Chunks.join(U32, Chunks.smap(~U32, ~U32, ~comp_oct, Chunks.of(U32, d, ws))))

def compress(d: Nat, +ws: B.Octets()) -> B.Octets():
  compress.go(fit(d, List.length(&2, U32, ws)), ws)

def compress_seq(d: Nat, +ws: B.Octets()) -> B.Octets():
  compress_seq.go(fit(d, List.length(&2, U32, ws)), ws)

def blobs(+bs: B.Bytes()) -> Chunks.Chunks<B.Byte>:
  +d = U32.to_nat(B.to_u32(byte_at(bs, 4n)))
  Chunks.of_list(B.Byte, d,
    split_chunks(pow2(d), List.drop(&2, B.Byte, bs, 5n), Nil{}))

def decompress(ws: B.Octets()) -> B.Octets():
  Chunks.join(U32, Chunks.pmap(~B.Byte, ~U32, ~decomp_oct, blobs(B.decode(ws))))

def decompress_seq(ws: B.Octets()) -> B.Octets():
  Chunks.join(U32, Chunks.smap(~B.Byte, ~U32, ~decomp_oct, blobs(B.decode(ws))))
