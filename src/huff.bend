import Base
import ./byte.bend as B
import ./bits.bend as Bits
import ./tab.bend as Tab

# A prefix code as a binary tree. `at` reads a path, `find` writes one,
# and `prefix` (in LAWS.bend) is the fact that ties them together.
type HTree is Data:
  HLeaf{sym: B.Sym}
  HNode{lo: HTree, hi: HTree}

# The symbol a complete path lands on.
def at(t: HTree, p: B.Bits()) -> Maybe<&2, B.Sym>:
  match t:
    case HLeaf{s}:
      match p:
        case Nil{}:
          Some{s}
        case Con{b, r}:
          None{}
    case HNode{lo, hi}:
      match p:
        case Nil{}:
          None{}
        case Con{b, r}:
          match b:
            case False{}:
              at(lo, r)
            case True{}:
              at(hi, r)

# Decoding consumes one bit per step and restarts at the root on every
# leaf, so it recurses on the bit stream and needs no fuel.
def decode(p: B.Bits(), +root: HTree, cur: HTree) -> List<&2, B.Sym>:
  match p:
    case Nil{}:
      Nil{}
    case Con{b, r}:
      match b:
        case False{}:
          match cur:
            case HLeaf{s}:
              Nil{}
            case HNode{lo, hi}:
              match lo:
                case HLeaf{s}:
                  Con{s, decode(r, root, root)}
                case HNode{a, c}:
                  decode(r, root, HNode{a, c})
        case True{}:
          match cur:
            case HLeaf{s}:
              Nil{}
            case HNode{lo, hi}:
              match hi:
                case HLeaf{s}:
                  Con{s, decode(r, root, root)}
                case HNode{a, c}:
                  decode(r, root, HNode{a, c})

def find.leaf(hit: Bool) -> Maybe<&2, B.Bits()>:
  match hit:
    case True{}:
      Some{Nil{}}
    case False{}:
      None{}

def find.node(a: Maybe<&2, B.Bits()>, b: Maybe<&2, B.Bits()>) ->
  Maybe<&2, B.Bits()>:
  match a:
    case Some{p}:
      Some{Con{False{}, p}}
    case None{}:
      match b:
        case Some{q}:
          Some{Con{True{}, q}}
        case None{}:
          None{}

# The path that reaches a symbol, if the tree holds it.
def find(t: HTree, +s: B.Sym) -> Maybe<&2, B.Bits()>:
  match t:
    case HLeaf{k}:
      find.leaf(B.eq_sym(k, s))
    case HNode{lo, hi}:
      find.node(find(lo, s), find(hi, s))

# ---------------------------------------------------------------- codes

# A symbol-indexed table of paths, so encoding is nine steps per symbol
# instead of a walk over the whole tree.
def Codes() -> Data:
  Tab.Tab<&2, B.Bits()>

def codes.go(t: HTree, +pre: B.Bits(), tab: Codes()) -> Codes():
  match t:
    case HLeaf{s}:
      Tab.set(B.Bits(), tab, B.sym_bits(s), List.reverse(&2, Bool, pre))
    case HNode{lo, hi}:
      codes.go(hi, Con{True{}, pre}, codes.go(lo, Con{False{}, pre}, tab))

def codes(t: HTree) -> Codes():
  codes.go(t, Nil{}, Tab.new(B.Bits(), 9n, Nil{}))

def encode(syms: List<&2, B.Sym>, +tab: Codes()) -> B.Bits():
  match syms:
    case Nil{}:
      Nil{}
    case Con{s, r}:
      List.append(&2, Bool, Tab.get(B.Bits(), tab, B.sym_bits(s)),
        encode(r, tab))

# ---------------------------------------------------- the length header

# The code lengths of the live alphabet, one byte each: literals 0..255
# plus the length and distance codes up to 314, rounded to 320. Both
# sides rebuild the very same tree from this table with `canon`, so the
# decoder's tree is the encoder's tree by construction, not by argument.
def ALPHA() -> Nat:
  320n

def LAST() -> Nat:
  319n

def lens_write(ls: B.Bytes()) -> B.Bits():
  Bits.unpack(ls)

def lens_read.put(y: B.Byte, pr: B.Bytes() & B.Bits()) -> B.Bytes() & B.Bits():
  (ys, rest) = pr
  (Con{y, ys}, rest)

def lens_read(n: Nat, p: B.Bits()) -> B.Bytes() & B.Bits():
  match n:
    case 0n:
      (Nil{}, p)
    case 1n+k:
      match p:
        case Nil{}:
          (Nil{}, Nil{})
        case Con{b0, r0}:
          match r0:
            case Nil{}:
              (Nil{}, Nil{})
            case Con{b1, r1}:
              match r1:
                case Nil{}:
                  (Nil{}, Nil{})
                case Con{b2, r2}:
                  match r2:
                    case Nil{}:
                      (Nil{}, Nil{})
                    case Con{b3, r3}:
                      match r3:
                        case Nil{}:
                          (Nil{}, Nil{})
                        case Con{b4, r4}:
                          match r4:
                            case Nil{}:
                              (Nil{}, Nil{})
                            case Con{b5, r5}:
                              match r5:
                                case Nil{}:
                                  (Nil{}, Nil{})
                                case Con{b6, r6}:
                                  match r6:
                                    case Nil{}:
                                      (Nil{}, Nil{})
                                    case Con{b7, r7}:
                                      lens_read.put(B.Byte{b0, b1, b2, b3, b4, b5, b6, b7}, lens_read(k, r7))

# --------------------------------------------------- canonical rebuild

# A tree under construction: `PEmpty` is a slot nothing has claimed yet.
type PTree is Data:
  PEmpty{}
  PLeaf{sym: B.Sym}
  PNode{lo: PTree, hi: PTree}

def put(p: B.Bits(), t: PTree, s: B.Sym) -> PTree:
  match p:
    case Nil{}:
      PLeaf{s}
    case Con{b, r}:
      match b:
        case False{}:
          match t:
            case PEmpty{}:
              PNode{put(r, PEmpty{}, s), PEmpty{}}
            case PLeaf{k}:
              PNode{put(r, PEmpty{}, s), PEmpty{}}
            case PNode{lo, hi}:
              PNode{put(r, lo, s), hi}
        case True{}:
          match t:
            case PEmpty{}:
              PNode{PEmpty{}, put(r, PEmpty{}, s)}
            case PLeaf{k}:
              PNode{PEmpty{}, put(r, PEmpty{}, s)}
            case PNode{lo, hi}:
              PNode{lo, put(r, hi, s)}

def solid(t: PTree) -> HTree:
  match t:
    case PEmpty{}:
      HLeaf{B.sym_from_nat(LAST())}
    case PLeaf{s}:
      HLeaf{s}
    case PNode{lo, hi}:
      HNode{solid(lo), solid(hi)}

def zeros(n: Nat) -> List<&2, Nat>:
  List.replicate(Nat, n, 0n)

def nth(xs: List<&2, Nat>, n: Nat) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, n), 0n)

def nat_bits.go(w: Nat, +n: Nat, acc: B.Bits()) -> B.Bits():
  match w:
    case 0n:
      acc
    case 1n+k:
      nat_bits.go(k, Nat.div(n, 2n), Con{Nat.is_eq(Nat.mod(n, 2n), 1n), acc})

def nat_bits(w: Nat, n: Nat) -> B.Bits():
  nat_bits.go(w, n, Nil{})

def bump(+acc: List<&2, Nat>, +l: Nat) -> List<&2, Nat>:
  match l:
    case 0n:
      acc
    case 1n+k:
      List.set(&2, Nat, acc, 1n+k, 1n+nth(acc, 1n+k))

def count_lens(ls: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      acc
    case Con{l, r}:
      count_lens(r, bump(acc, l))

# next_code[len] = (next_code[len-1] + count[len-1]) * 2
def next_codes(cs: List<&2, Nat>, +code: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      Con{code, next_codes(r, Nat.mul(Nat.add(code, c), 2n))}

def assign(ls: List<&2, Nat>, +i: Nat, +nexts: List<&2, Nat>, t: PTree) -> PTree:
  match ls:
    case Nil{}:
      t
    case Con{l, r}:
      match l:
        case 0n:
          assign(r, 1n+i, nexts, t)
        case 1n+k:
          +w = {1n+k : Nat}
          +code = nth(nexts, w)
          assign(r, 1n+i, List.set(&2, Nat, nexts, w, 1n+code),
            put(nat_bits(w, code), t, B.sym_from_nat(i)))

def lens_of(lb: B.Bytes()) -> List<&2, Nat>:
  match lb:
    case Nil{}:
      Nil{}
    case Con{y, r}:
      Con{U32.to_nat(B.to_u32(y)), lens_of(r)}

def bytes_of_lens(ls: List<&2, Nat>) -> B.Bytes():
  match ls:
    case Nil{}:
      Nil{}
    case Con{n, r}:
      Con{B.from_u32(U32.from_nat(n)), bytes_of_lens(r)}

# The longest code length the canonical builder tracks. `next_codes`
# doubles once per length, so this also bounds the largest code value at
# 2^MAXBITS -- well inside Bend's 2^48 immediate. A Huffman code over a
# chunk of W bytes is at most ~1.44*log2(W) bits deep, so 40 leaves ample
# room for the chunk sizes this codec uses.
def MAXBITS() -> Nat:
  40n

# The one function both sides call: a length table in, a tree out.
def canon(lb: B.Bytes()) -> HTree:
  +ls = lens_of(lb)
  solid(assign(ls, 0n, next_codes(count_lens(ls, zeros(MAXBITS())), 0n),
    PEmpty{}))

# ------------------------------------------------- building the lengths

type HN is Data:
  HN{w: Nat, t: PTree}

def hn_le(a: HN, b: HN) -> Bool:
  match a:
    case HN{wa, ta}:
      match b:
        case HN{wb, tb}:
          Nat.is_le(wa, wb)

def hn_join(a: HN, b: HN) -> HN:
  match a:
    case HN{wa, ta}:
      match b:
        case HN{wb, tb}:
          HN{Nat.add(wa, wb), PNode{ta, tb}}

def hn_tree(a: HN) -> PTree:
  match a:
    case HN{w, t}:
      t

def nodes(fs: List<&2, Nat>, +i: Nat) -> List<&2, HN>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, r}:
      match f:
        case 0n:
          nodes(r, 1n+i)
        case 1n+k:
          Con{HN{1n+k, PLeaf{B.sym_from_nat(i)}}, nodes(r, 1n+i)}

def merge(f: Nat, xs: List<&2, HN>) -> PTree:
  match f:
    case 0n:
      PEmpty{}
    case 1n+g:
      match xs:
        case Nil{}:
          PEmpty{}
        case Con{a, r1}:
          match r1:
            case Nil{}:
              hn_tree(a)
            case Con{b, r2}:
              merge(g, List.sort(~HN, ~hn_le, Con{hn_join(a, b), r2}))

def depths(t: PTree, +d: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case PEmpty{}:
      acc
    case PLeaf{s}:
      List.set(&2, Nat, acc, B.sym_to_nat(s), d)
    case PNode{lo, hi}:
      depths(hi, 1n+d, depths(lo, 1n+d, acc))

# A one-leaf tree would give that symbol a zero-length code, so make
# sure at least two symbols are live before building.
def live(fs: List<&2, Nat>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{f, r}:
      match f:
        case 0n:
          live(r)
        case 1n+k:
          1n+live(r)

def pad(fs: List<&2, Nat>, n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      List.set(&2, Nat, List.set(&2, Nat, fs, 0n, 1n), LAST(), 1n)
    case 1n+k:
      match k:
        case 0n:
          List.set(&2, Nat, fs, LAST(), 1n)
        case 1n+j:
          fs

def build(+fs: List<&2, Nat>) -> B.Bytes():
  +ps = pad(List.take(&2, Nat, fs, ALPHA()), live(List.take(&2, Nat, fs, ALPHA())))
  bytes_of_lens(depths(merge(ALPHA(), List.sort(~HN, ~hn_le, nodes(ps, 0n))),
    0n, zeros(ALPHA())))
