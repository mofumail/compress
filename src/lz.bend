import Base
import ./byte.bend as B
import ./tab.bend as Tab

# A token stream: a literal byte, or "go back `dist` bytes and copy
# `len` of them". `dist` may be smaller than `len`, which is how runs
# are encoded, and `copy` below reproduces that overlap exactly.
type Tok is Data:
  Lit{b: B.Byte}
  Ref{dist: Nat, len: Nat}

def MINLEN() -> Nat:
  3n

def MAXLEN() -> Nat:
  258n

# ------------------------------------------------------- the decoder

def zero() -> B.Byte:
  B.Byte{False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}}

# The byte `d` places back in the history (which is stored reversed, so
# the most recent byte is at the head).
def back(h: B.Bytes(), d: Nat) -> B.Byte:
  Maybe.default(&2, B.Byte, List.get(&2, B.Byte, h, Nat.sub(d, 1n)), zero())

# One byte at a time, so a distance smaller than the length reads back
# the bytes this very loop just wrote.
def copy(l: Nat, +d: Nat, +h: B.Bytes()) -> B.Bytes():
  match l:
    case 0n:
      h
    case 1n+k:
      copy(k, d, Con{back(h, d), h})

# Tokens to output, newest byte first.
def expand(ts: List<&2, Tok>, +h: B.Bytes()) -> B.Bytes():
  match ts:
    case Nil{}:
      h
    case Con{t, r}:
      match t:
        case Lit{b}:
          expand(r, Con{b, h})
        case Ref{d, l}:
          expand(r, copy(l, d, h))

def expand_all(ts: List<&2, Tok>) -> B.Bytes():
  List.reverse(&2, B.Byte, expand(ts, Nil{}))

# ------------------------------------------------------- the encoder

def heads_eq(xs: B.Bytes(), ys: B.Bytes()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{a, r}:
      match ys:
        case Nil{}:
          False{}
        case Con{b, s}:
          B.eq_byte(a, b)

# The length of the common prefix of two suffixes of the same chunk,
# capped by `f`. The comparison of the two heads arrives as a parameter
# because Bend has no mutual recursion to branch through.
def lcp(+xs: B.Bytes(), +ys: B.Bytes(), f: Nat, same: Bool) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{a, r}:
      match ys:
        case Nil{}:
          0n
        case Con{b, s}:
          match f:
            case 0n:
              0n
            case 1n+g:
              match same:
                case False{}:
                  0n
                case True{}:
                  1n+lcp(r, s, g, heads_eq(r, s))

def lcp_of(+xs: B.Bytes(), +ys: B.Bytes()) -> Nat:
  lcp(xs, ys, MAXLEN(), heads_eq(xs, ys))

# The table is 2^HBITS wide and keyed by a multiplicative hash of the
# next three bytes. Picking bits straight out of the bytes clusters
# badly on text (the high bits of ASCII barely move), so the 24 bits go
# through a Knuth multiply first and the top HBITS come off the result.
def HBITS() -> Nat:
  15n

def key_of(+w: U32) -> B.Bits():
  [B.bit(w, 14n), B.bit(w, 13n), B.bit(w, 12n),
   B.bit(w, 11n), B.bit(w, 10n), B.bit(w, 9n), B.bit(w, 8n),
   B.bit(w, 7n), B.bit(w, 6n), B.bit(w, 5n), B.bit(w, 4n),
   B.bit(w, 3n), B.bit(w, 2n), B.bit(w, 1n), B.bit(w, 0n)]

def key3(a: B.Byte, b: B.Byte, c: B.Byte) -> B.Bits():
  key_of(U32.shrn(U32.mul((B.to_u32(a) * 65536 + B.to_u32(b) * 256 +
    B.to_u32(c) : U32), 2654435761), 17n))

def key(xs: B.Bytes()) -> B.Bits():
  match xs:
    case Nil{}:
      key_of(0)
    case Con{a, r}:
      match r:
        case Nil{}:
          key_of(1)
        case Con{b, s}:
          match s:
            case Nil{}:
              key_of(2)
            case Con{c, u}:
              key3(a, b, c)

# The match finder: a hash of three bytes to a short chain of the
# positions it was last seen at, each carrying the chunk's suffix from
# there. Holding the suffix means checking a candidate is a plain
# two-list walk with no random access.
type Slot is Data:
  SNone{}
  SAt{pos: Nat, suf: B.Bytes(), nxt: Slot}

type Best is Data:
  Best{len: Nat, dist: Nat}

def HTab() -> Data:
  Tab.Tab<&2, Slot>

# How many candidates per hash bucket to try. Every candidate is walked
# (Bend has no lazy branch inside a recursive position), so this trades
# time for ratio directly.
def CHAIN() -> Nat:
  4n

# The distance table reaches 32768, so a candidate further back than
# that cannot be encoded and is refused here rather than silently
# truncated. This is the same window gzip uses.
def MAXDIST() -> Nat:
  U32.to_nat(32768)

def trunc(k: Nat, c: Slot) -> Slot:
  match k:
    case 0n:
      SNone{}
    case 1n+j:
      match c:
        case SNone{}:
          SNone{}
        case SAt{p, s, n}:
          SAt{p, s, trunc(j, n)}

def push(+tab: HTab(), +xs: B.Bytes(), +pos: Nat) -> HTab():
  +k = key(xs)
  Tab.set(Slot, tab, k, SAt{pos, xs, trunc(CHAIN(), Tab.get(Slot, tab, k))})

# Every position a token covers goes into the table, not just the one it
# starts at: matches found inside an earlier match are most of the win.
def ins_range(k: Nat, +tab: HTab(), +xs: B.Bytes(), +pos: Nat) -> HTab():
  match k:
    case 0n:
      tab
    case 1n+j:
      match xs:
        case Nil{}:
          tab
        case Con{x, r}:
          ins_range(j, push(tab, xs, pos), r, 1n+pos)

def blen(x: Best) -> Nat:
  match x:
    case Best{l, d}:
      l

def better(+a: Best, +b: Best) -> Best:
  Bool.pick(Best, Nat.is_lt(blen(a), blen(b)), b, a)

def best_of(k: Nat, +pos: Nat, +xs: B.Bytes(), c: Slot, +b: Best) -> Best:
  match k:
    case 0n:
      b
    case 1n+j:
      match c:
        case SNone{}:
          b
        case SAt{p, s, n}:
          +d = Nat.sub(pos, p)
          best_of(j, pos, xs, n, Bool.pick(Best,
            Nat.is_le(d, MAXDIST()), better(b, Best{lcp_of(s, xs), d}), b))

def find_best(+tab: HTab(), +pos: Nat, +xs: B.Bytes()) -> Best:
  best_of(CHAIN(), pos, xs, Tab.get(Slot, tab, key(xs)), Best{0n, 0n})

# The greedy parse. `b` is the candidate match for the current position,
# computed by the previous step: Bend can only match on parameters, so
# the decision has to arrive as one. `f` bounds the number of tokens
# (each consumes at least one byte).
def parse(f: Nat, +xs: B.Bytes(), +pos: Nat, +tab: HTab(),
  acc: List<&2, Tok>, b: Best) -> List<&2, Tok>:
  match f:
    case 0n:
      List.reverse(&2, Tok, acc)
    case 1n+g:
      match xs:
        case Nil{}:
          List.reverse(&2, Tok, acc)
        case Con{x, r}:
          match b:
            case Best{l, d}:
              match l:
                case 0n:
                  +t2 = push(tab, xs, pos)
                  +p2 = {1n+pos : Nat}
                  parse(g, r, p2, t2, Con{Lit{x}, acc}, find_best(t2, p2, r))
                case 1n+k:
                  match k:
                    case 0n:
                      +t2 = push(tab, xs, pos)
                      +p2 = {1n+pos : Nat}
                      parse(g, r, p2, t2, Con{Lit{x}, acc},
                        find_best(t2, p2, r))
                    case 1n+j:
                      match j:
                        case 0n:
                          +t2 = push(tab, xs, pos)
                          +p2 = {1n+pos : Nat}
                          parse(g, r, p2, t2, Con{Lit{x}, acc},
                            find_best(t2, p2, r))
                        case 1n+m:
                          +ll = {3n+m : Nat}
                          +t2 = ins_range(ll, tab, xs, pos)
                          +xs2 = List.drop(&2, B.Byte, xs, ll)
                          +p2 = Nat.add(pos, ll)
                          parse(g, xs2, p2, t2, Con{Ref{d, ll}, acc},
                            find_best(t2, p2, xs2))

def parse_all(+w: B.Bytes()) -> List<&2, Tok>:
  +t0 = Tab.new(Slot, HBITS(), SNone{})
  parse(List.length(&2, B.Byte, w), w, 0n, t0, Nil{}, find_best(t0, 0n, w))

# The trivial parse: every byte a literal. The LZ layer's base case,
# and what the parser falls back to when no candidate matches.
def lits(xs: B.Bytes()) -> List<&2, Tok>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{b, r}:
      Con{Lit{b}, lits(r)}

# --------------------------------------------------- the fast decoder

# `expand` above is the reference decoder the laws speak about. Its
# history is a list, so `back` walks `d` cells for every copied byte --
# O(n * window). This one keeps the last 32 KiB in an in-place Array
# ring (2^15 slots: exactly the window, and Array indexes wrap around),
# so a copied byte costs one read and one write of 15 levels each.
# It is checked against `expand` by test/decode_test.bend.
def Ring() -> Type:
  Array<U32>

def copy_go(l: Nat, +d: U32, +pos: U32, pr: Array<U32> & U32,
  acc: List<&2, B.Byte>) -> Array<U32> & List<&2, B.Byte>:
  match l:
    case 0n:
      (a, v) = pr
      (a, acc)
    case 1n+k:
      (a, +v) = pr
      +p1 = (pos + 1 : U32)
      copy_go(k, d, p1, Array.get(U32, Array.set(U32, a, pos, v), (p1 - d : U32)),
        Con{B.from_u32(v), acc})

def expand_fast(+ts: List<&2, Tok>, +pos: U32,
  st: Array<U32> & List<&2, B.Byte>) -> List<&2, B.Byte>:
  match ts:
    case Nil{}:
      (a, acc) = st
      List.reverse(&2, B.Byte, acc)
    case Con{t, r}:
      match t:
        case Lit{b}:
          (a, acc) = st
          expand_fast(r, (pos + 1 : U32),
            (Array.set(U32, a, pos, B.to_u32(b)), Con{b, acc}))
        case Ref{d, l}:
          (a, acc) = st
          +dd = U32.from_nat(d)
          expand_fast(r, (pos + U32.from_nat(l) : U32),
            copy_go(l, dd, pos, Array.get(U32, a, (pos - dd : U32)), acc))

def expand_fast_all(+ts: List<&2, Tok>) -> B.Bytes():
  expand_fast(ts, 0, ([0 : U32^15n], Nil{}))
