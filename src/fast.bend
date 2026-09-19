import Base
import ./byte.bend as B
import ./huff.bend as Huff

# ======================================================================
# The fast codec.
#
# Same container and bitstream as src/codec.bend (the proven reference),
# so the reference decoder can read what this encoder writes and vice
# versa -- test/fast_test.bend checks both directions. The difference is
# representation: every byte, token, table and bit buffer here is a U32
# in a flat Array<U32>, which Bend compiles to a native buffer, instead
# of a list of eight-Bool records.
#
# Bend has no mutual recursion and cannot destructure a computed value,
# so every loop below has one shape: a self-recursive driver
# `loop(fuel, state)` that matches a flag in its state record, and a
# chain of non-recursive helpers `step`, `step.b`, ... that each do one
# array access and pass the result on as a parameter.
# ======================================================================

def A() -> Type:
  Array<U32>

def WMASK() -> U32:
  32767

def MAXDIST() -> U32:
  32768

def CHAIN() -> Nat:
  8n

# Positions inside a match longer than this are not hashed (zlib's
# max_insert_length): long matches mean repetitive data, where the table
# is already well stocked.
def INSMAX() -> U32:
  258

# Stop walking the chain once a match this long is found.
def NICE() -> U32:
  64

def lt(+a: U32, +b: U32) -> Bool:
  U32.is_lt(a, b)

# ------------------------------------------------------------- tables
#
# One 2048-slot table holds everything the length/distance coding needs:
#   [0, 256)     length code for len-3        (len 3..258)
#   [256, 768)   distance code for dist, via dslot
#   [768, 797)   length base      [800, 829) length extra bits
#   [832, 862)   distance base    [864, 894) distance extra bits

def LBASE() -> List<&2, U32>:
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
   67, 83, 99, 115, 131, 163, 195, 227, 258]

def LEXT() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4,
   5, 5, 5, 5, 0]

def DBASE() -> List<&2, U32>:
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
   769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

def DEXT() -> List<&2, U32>:
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
   11, 11, 12, 12, 13, 13]

# Where distance `d` (1..32768) lives in the table: small distances get a
# slot each, larger ones share a slot per 128 (every code boundary past
# 256 is 1 mod 128, so no slot straddles two codes).
def dslot(+d: U32) -> U32:
  Bool.pick(U32, lt((d - 1 : U32), 256), (256 + d - 1 : U32),
    (512 + ((d - 1 : U32) >> 7n) : U32))

def put_list(xs: List<&2, U32>, +at: U32, t: A()) -> A():
  match xs:
    case Nil{}:
      t
    case Con{+x, r}:
      put_list(r, (at + 1 : U32), Array.set(U32, t, at, x))

# t[lo .. lo + cnt) := v, for the length codes (slot = len - 3).
def fill_len(f: Nat, +len: U32, +v: U32, t: A()) -> A():
  match f:
    case 0n:
      t
    case 1n+g:
      fill_len(g, (len + 1 : U32), v, Array.set(U32, t, (len - 3 : U32), v))

# Distances past 256 share one slot per 128, so a code with >= 7 extra
# bits needs only 2^(e-7) writes, stepping 128 at a time.
def fill_dist(f: Nat, +d: U32, +step: U32, +v: U32, t: A()) -> A():
  match f:
    case 0n:
      t
    case 1n+g:
      fill_dist(g, (d + step : U32), step, v, Array.set(U32, t, dslot(d), v))

def codes_len(bs: List<&2, U32>, es: List<&2, U32>, +k: U32, t: A()) -> A():
  match bs:
    case Nil{}:
      t
    case Con{+b, br}:
      match es:
        case Nil{}:
          t
        case Con{+e, er}:
          codes_len(br, er, (k + 1 : U32),
            fill_len(Nat.pow(2n, U32.to_nat(e)), b, k, t))

def codes_dist(bs: List<&2, U32>, es: List<&2, U32>, +k: U32, t: A()) -> A():
  match bs:
    case Nil{}:
      t
    case Con{+b, br}:
      match es:
        case Nil{}:
          t
        case Con{+e, er}:
          +wide = U32.is_le(7, e)
          codes_dist(br, er, (k + 1 : U32),
            fill_dist(Nat.pow(2n, U32.to_nat(Bool.pick(U32, wide, (e - 7 : U32), e))), b,
              Bool.pick(U32, wide, 128, 1), k, t))

def tables() -> A():
  codes_dist(DBASE(), DEXT(), 0,
    codes_len(LBASE(), LEXT(), 0,
      put_list(DEXT(), 864, put_list(DBASE(), 832,
        put_list(LEXT(), 800, put_list(LBASE(), 768, [0 : U32^13n]))))))

# the hash of the three bytes at the top of a packed word
def hash4(+v: U32) -> U32:
  ((v >> 8n : U32) * 2654435761 >> 17n : U32)

def get(a: A(), +i: U32) -> A() & U32:
  Array.get(U32, a, i)

# ------------------------------------------------ match length: w[i..] vs w[j..]

type MS is Type:
  MS{w: Array<U32>, i: U32, j: U32, l: U32, lim: U32, go: Bool}

# `w` holds, at each position, that position's next four bytes packed
# big-endian (see `win`), so one comparison covers four bytes and the
# first differing byte falls out of the XOR of two words.
def eq_bytes(+x: U32) -> U32:
  Bool.pick(U32, lt(x, 256), 3, Bool.pick(U32, lt(x, 65536), 2,
    Bool.pick(U32, lt(x, 16777216), 1, 0)))

def ms.c(+i: U32, +j: U32, +l: U32, +lim: U32, +x: U32, pr: A() & U32) -> MS:
  (w, +y) = pr
  +d = (x .^. y : U32)
  +whole = U32.is_eq(d, 0)
  +l1 = U32.min(lim, (l + Bool.pick(U32, whole, 4, eq_bytes(d)) : U32))
  MS{w, (i + 4 : U32), (j + 4 : U32), l1, lim, Bool.and(whole, lt(l1, lim))}

def ms.b(+i: U32, +j: U32, +l: U32, +lim: U32, pr: A() & U32) -> MS:
  (w, +x) = pr
  ms.c(i, j, l, lim, x, get(w, j))

def ms.loop(f: Nat, s: MS) -> MS:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case MS{w, +i, +j, +l, +lim, go}:
          match go:
            case False{}:
              MS{w, i, j, l, lim, False{}}
            case True{}:
              ms.loop(g, ms.b(i, j, l, lim, get(w, i)))

# ------------------------------------------------ the hash chain

# `best` packs a match as (len << 16) | (dist - 1).
type CS is Type:
  CS{w: Array<U32>, prev: Array<U32>, pos: U32, n: U32, c: U32, best: U32,
    live: Bool}

def blen(+best: U32) -> U32:
  (best >> 16n : U32)

def cs.live(+pos: U32, +c: U32, +best: U32) -> Bool:
  Bool.and(U32.is_ne(c, 0), Bool.and(
    U32.is_le((pos - (c - 1 : U32) : U32), MAXDIST()), lt(blen(best), NICE())))

def cs.c(w: A(), +pos: U32, +n: U32, +best: U32, pr: A() & U32) -> CS:
  (prev, +nc) = pr
  CS{w, prev, pos, n, nc, best, cs.live(pos, nc, best)}

def cs.b(prev: A(), +pos: U32, +n: U32, +c: U32, +best: U32, m: MS) -> CS:
  match m:
    case MS{w, i, j, +l, lim, go}:
      +cp = (c - 1 : U32)
      +nb = Bool.pick(U32, lt(blen(best), l),
        ((l << 16n) .|. (pos - cp - 1 : U32) : U32), best)
      cs.c(w, pos, n, nb, get(prev, (cp .&. WMASK() : U32)))

def cs.step(w: A(), prev: A(), +pos: U32, +n: U32, +c: U32, +best: U32) -> CS:
  +lim = U32.min(258, (n - pos : U32))
  cs.b(prev, pos, n, c, best,
    ms.loop(65n, MS{w, (c - 1 : U32), pos, 0, lim, lt(0, lim)}))

def cs.loop(f: Nat, s: CS) -> CS:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CS{w, prev, +pos, +n, +c, +best, live}:
          match live:
            case False{}:
              CS{w, prev, pos, n, c, best, False{}}
            case True{}:
              cs.loop(g, cs.step(w, prev, pos, n, c, best))

# ------------------------------------------------ inserting one position

# head[hash(w[q..q+2])] := q + 1, prev[q & WMASK] := the old head.
type HS is Type:
  HS{w: Array<U32>, head: Array<U32>, prev: Array<U32>, cand: U32}

def hs.e(w: A(), prev: A(), +q: U32, pr: A() & U32) -> HS:
  (head, +cand) = pr
  HS{w, head, Array.set(U32, prev, (q .&. WMASK() : U32), cand), cand}

def hs.b(head: A(), prev: A(), +q: U32, pr: A() & U32) -> HS:
  (w, +v) = pr
  hs.e(w, prev, q, Array.swap(U32, head, hash4(v), (q + 1 : U32)))

def insert(w: A(), head: A(), prev: A(), +q: U32) -> HS:
  hs.b(head, prev, q, get(w, q))

type IS is Type:
  IS{w: Array<U32>, head: Array<U32>, prev: Array<U32>, q: U32, end: U32,
    go: Bool}

def is.b(+q: U32, +end: U32, h: HS) -> IS:
  match h:
    case HS{w, head, prev, c}:
      +q1 = (q + 1 : U32)
      IS{w, head, prev, q1, end, lt(q1, end)}

def ins.loop(f: Nat, s: IS) -> IS:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case IS{w, head, prev, +q, +end, go}:
          match go:
            case False{}:
              IS{w, head, prev, q, end, False{}}
            case True{}:
              ins.loop(g, is.b(q, end, insert(w, head, prev, q)))

# ------------------------------------------------ the parse

def inc.b(+i: U32, pr: A() & U32) -> A():
  (f, +v) = pr
  Array.set(U32, f, i, (v + 1 : U32))

def inc(f: A(), +i: U32) -> A():
  inc.b(i, get(f, i))

# tok[k] is a literal byte, or 0x80000000 | (len << 16) | (dist - 1).
type PS is Type:
  PS{w: Array<U32>, head: Array<U32>, prev: Array<U32>, tok: Array<U32>,
    freq: Array<U32>, t: Array<U32>, n: U32, pos: U32, nt: U32, more: Bool}

def ps.m4(tok: A(), freq: A(), t: A(), +n: U32, +nt: U32, +next: U32, s: IS) -> PS:
  match s:
    case IS{w, head, prev, q, end, go}:
      PS{w, head, prev, tok, freq, t, n, next, nt, lt(next, n)}

def ps.m3(w: A(), head: A(), prev: A(), tok: A(), freq: A(), +n: U32,
  +pos: U32, +nt: U32, +len: U32, pr: A() & U32) -> PS:
  (t, +di) = pr
  +q = (pos + 1 : U32)
  +end = (pos + Bool.pick(U32, U32.is_le(len, INSMAX()), len, 1) : U32)
  ps.m4(tok, inc(freq, (285 + di : U32)), t, n, (nt + 1 : U32), (pos + len : U32),
    ins.loop(257n, IS{w, head, prev, q, end, lt(q, end)}))

def ps.m2(w: A(), head: A(), prev: A(), tok: A(), freq: A(), +n: U32,
  +pos: U32, +nt: U32, +len: U32, +dist: U32, pr: A() & U32) -> PS:
  (t, +li) = pr
  ps.m3(w, head, prev, tok, inc(freq, (256 + li : U32)), n, pos, nt, len,
    get(t, dslot(dist)))

def ps.match(w: A(), head: A(), prev: A(), tok: A(), freq: A(), t: A(),
  +n: U32, +pos: U32, +nt: U32, +best: U32) -> PS:
  +len = blen(best)
  ps.m2(w, head, prev, Array.set(U32, tok, nt, (best .|. 2147483648 : U32)),
    freq, n, pos, nt, len, ((best .&. 65535 : U32) + 1 : U32),
    get(t, (len - 3 : U32)))

def ps.lit(head: A(), prev: A(), tok: A(), freq: A(), t: A(), +n: U32,
  +pos: U32, +nt: U32, pr: A() & U32) -> PS:
  (w, +v) = pr
  +a = (v >> 24n : U32)
  +p1 = (pos + 1 : U32)
  PS{w, head, prev, Array.set(U32, tok, nt, a), inc(freq, a), t, n, p1,
    (nt + 1 : U32), lt(p1, n)}

def ps.d(is_match: Bool, w: A(), head: A(), prev: A(), tok: A(), freq: A(),
  t: A(), +n: U32, +pos: U32, +nt: U32, +best: U32) -> PS:
  match is_match:
    case False{}:
      ps.lit(head, prev, tok, freq, t, n, pos, nt, get(w, pos))
    case True{}:
      ps.match(w, head, prev, tok, freq, t, n, pos, nt, best)

def ps.c(head: A(), tok: A(), freq: A(), t: A(), +n: U32, +pos: U32,
  +nt: U32, cs: CS) -> PS:
  match cs:
    case CS{w, prev, p, m, c, +best, live}:
      ps.d(lt(2, blen(best)), w, head, prev, tok, freq, t, n, pos, nt, best)

def ps.b(+chain: Nat, tok: A(), freq: A(), t: A(), +n: U32, +pos: U32, +nt: U32,
  h: HS) -> PS:
  match h:
    case HS{w, head, prev, +cand}:
      ps.c(head, tok, freq, t, n, pos, nt,
        cs.loop(chain, CS{w, prev, pos, n, cand, 0, cs.live(pos, cand, 0)}))

# `chain`: how many candidates to try per position (see CHAIN)
def ps.loop(f: Nat, +chain: Nat, s: PS) -> PS:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case PS{w, head, prev, tok, freq, t, +n, +pos, +nt, more}:
          match more:
            case False{}:
              PS{w, head, prev, tok, freq, t, n, pos, nt, False{}}
            case True{}:
              ps.loop(g, chain, ps.b(chain, tok, freq, t, n, pos, nt,
                insert(w, head, prev, pos)))

# The smallest d with 2^d >= n (at least 1).
def depth(f: Nat, +d: Nat, +n: U32) -> Nat:
  match f:
    case 0n:
      d
    case 1n+g:
      Bool.pick(Nat, U32.is_le(n, U32.pow(2, d)), d, depth(g, 1n+d, n))

def fill(xs: List<&2, U32>, +i: U32, w: A()) -> A():
  match xs:
    case Nil{}:
      w
    case Con{+x, r}:
      fill(r, (i + 1 : U32), Array.set(U32, w, i, x))

def arr_list(f: Nat, +i: U32, pr: A() & U32, acc: List<&2, U32>) -> List<&2, U32>:
  match f:
    case 0n:
      acc
    case 1n+g:
      (a, +v) = pr
      arr_list(g, (i - 1 : U32), get(a, (i - 2 : U32)), Con{v, acc})

def to_list(a: A(), +k: U32) -> List<&2, U32>:
  arr_list(U32.to_nat(k), k, get(a, (k - 1 : U32)), Nil{})

def toks(s: PS) -> List<&2, U32>:
  match s:
    case PS{w, head, prev, tok, freq, t, n, pos, +nt, more}:
      to_list(tok, nt)

# ======================================================================
# Encoding: canonical codes, then the bit writer.
#
# `L` is one 4096-slot lookup array per chunk:
#   [0, 2048)      the length/distance tables from `tables`
#   [2048, 2560)   code[sym]        [2560, 3072)  code length[sym]
#   [3072, 3136)   count[len]       [3136, 3200)  next_code[len]
# ======================================================================

def CODE() -> U32:
  2048

def CLEN() -> U32:
  2560

def CNT() -> U32:
  3072

def NXT() -> U32:
  3136

type R2 is Type:
  R2{a: Array<U32>, x: U32, y: U32}

def g2.b(+x: U32, pr: A() & U32) -> R2:
  (a, +y) = pr
  R2{a, x, y}

def g2.a(+j: U32, pr: A() & U32) -> R2:
  (a, +x) = pr
  g2.b(x, get(a, j))

def get2(a: A(), +i: U32, +j: U32) -> R2:
  g2.a(j, get(a, i))

# count[len] += 1 for every symbol with a code
def counts(ls: List<&2, U32>, l: A()) -> A():
  match ls:
    case Nil{}:
      l
    case Con{+n, r}:
      counts(r, inc(l, (CNT() + n : U32)))

# next[len] = (next[len-1] + count[len-1]) << 1, count[0] taken as 0
def nexts.b(+len: U32, r: R2) -> A():
  match r:
    case R2{l, +nx, +ct}:
      Array.set(U32, l, (NXT() + len : U32), ((nx + ct : U32) << 1n : U32))

def nexts(f: Nat, +len: U32, l: A()) -> A():
  match f:
    case 0n:
      l
    case 1n+g:
      nexts(g, (len + 1 : U32), nexts.b(len,
        get2(l, (NXT() + len - 1 : U32), (CNT() + len - 1 : U32))))

# code[sym] = next[len]++, in symbol order -- exactly Huff.canon's order,
# so the reference decoder rebuilds the same code from the same lengths.
def assign.b(+sym: U32, +len: U32, pr: A() & U32) -> A():
  (l, +c) = pr
  Array.set(U32, Array.set(U32, Array.set(U32, l, (NXT() + len : U32),
    (c + 1 : U32)), (CODE() + sym : U32), c), (CLEN() + sym : U32), len)

def assign.sel(unused: Bool, +sym: U32, +len: U32, l: A()) -> A():
  match unused:
    case True{}:
      l
    case False{}:
      assign.b(sym, len, get(l, (NXT() + len : U32)))

def assign(ls: List<&2, U32>, +sym: U32, l: A()) -> A():
  match ls:
    case Nil{}:
      l
    case Con{+len, r}:
      assign(r, (sym + 1 : U32), assign.sel(U32.is_eq(len, 0), sym, len, l))

def canon(+ls: List<&2, U32>, l: A()) -> A():
  assign(ls, 0, nexts(40n, 1, Array.set(U32, counts(ls, l), CNT(), 0)))

# ------------------------------------------------ the bit writer
# MSB-first, like Bits.pack. The `nacc` (< 8) pending bits sit at the
# TOP of `acc`; a put ORs the new bits in just below them, writes the top
# two bytes unconditionally (a partial byte is simply rewritten by the
# next put), and advances by the number of whole bytes. At most 7 + 16
# bits are ever pending, so nothing overflows and nothing branches.

type W is Type:
  W{out: Array<U32>, acc: U32, nacc: U32, opos: U32}

def shl(+a: U32, +n: U32) -> U32:
  U32.shln(a, U32.to_nat(n))

def shr(+a: U32, +n: U32) -> U32:
  U32.shrn(a, U32.to_nat(n))

def put16(w: W, +v: U32, +n: U32) -> W:
  match w:
    case W{out, +acc, +nacc, +opos}:
      +a = (acc .|. shl((v .&. (shl(1, n) - 1 : U32) : U32),
        ((32 - nacc - n : U32) .&. 31 : U32)) : U32)
      +t = (nacc + n : U32)
      +k = (t >> 3n : U32)
      W{Array.set(U32, Array.set(U32, out, opos, (a >> 24n : U32)),
          (opos + 1 : U32), ((a >> 16n : U32) .&. 255 : U32)),
        shl(a, (k << 3n : U32)), (t .&. 7 : U32), (opos + k : U32)}

def put.sel(big: Bool, w: W, +v: U32, +n: U32) -> W:
  match big:
    case False{}:
      put16(w, v, n)
    case True{}:
      put16(put16(w, shr(v, 16), (n - 16 : U32)), (v .&. 65535 : U32), 16)

def put(w: W, +v: U32, +n: U32) -> W:
  put.sel(lt(16, n), w, v, n)

# the final partial byte, padded with zero bits (already zero in `acc`)
def flush(w: W) -> W:
  match w:
    case W{out, +acc, +nacc, +opos}:
      W{Array.set(U32, out, opos, (acc >> 24n : U32)), 0, 0,
        (opos + Bool.pick(U32, U32.is_eq(nacc, 0), 0, 1) : U32)}

# ------------------------------------------------ the two passes
# Pass A writes every symbol's code; pass B, straight after it in the
# same bit stream, writes the extra bits of every length and distance.

type ES is Type:
  ES{tok: Array<U32>, l: Array<U32>, w: W, k: U32, nt: U32, bits: U32,
    b: Bool, go: Bool}

def es.put2.b(tok: A(), w: W, +k: U32, +nt: U32, +bits: U32, +pb: Bool,
  +n1: U32, +dist: U32, r2: R2) -> ES:
  match r2:
    case R2{l, +x3, +x4}:
      +k1 = (k + 1 : U32)
      ES{tok, l, put(w, Bool.pick(U32, pb, (dist - x3 : U32), x3), x4), k1, nt,
        (bits + Bool.pick(U32, pb, 0, (n1 + x4 : U32)) : U32), pb, lt(k1, nt)}

# two (value, width) pairs: r1 = (x1, x2) then r2 = (x3, x4)
def es.put2(tok: A(), w: W, +k: U32, +nt: U32, +bits: U32, +pb: Bool,
  +len: U32, +dist: U32, +i3: U32, +i4: U32, r1: R2) -> ES:
  match r1:
    case R2{l, +x1, +x2}:
      +v1 = Bool.pick(U32, pb, (len - x1 : U32), x1)
      es.put2.b(tok, put(w, v1, x2), k, nt, bits, pb, x2, dist, get2(l, i3, i4))

def es.match.b(tok: A(), w: W, +k: U32, +nt: U32, +bits: U32, +pb: Bool,
  +len: U32, +dist: U32, r: R2) -> ES:
  match r:
    case R2{l, +li, +di}:
      # pass A: codes of 256+li and 285+di; pass B: base/extra of li, di
      +i1 = Bool.pick(U32, pb, (768 + li : U32), (CODE() + 256 + li : U32))
      +i2 = Bool.pick(U32, pb, (800 + li : U32), (CLEN() + 256 + li : U32))
      +i3 = Bool.pick(U32, pb, (832 + di : U32), (CODE() + 285 + di : U32))
      +i4 = Bool.pick(U32, pb, (864 + di : U32), (CLEN() + 285 + di : U32))
      es.put2(tok, w, k, nt, bits, pb, len, dist, i3, i4, get2(l, i1, i2))

def es.lit.b(tok: A(), w: W, +k: U32, +nt: U32, +bits: U32, +pb: Bool,
  r: R2) -> ES:
  match r:
    case R2{l, +c, +n}:
      +k1 = (k + 1 : U32)
      +nn = Bool.pick(U32, pb, 0, n)
      ES{tok, l, put(w, c, nn), k1, nt, (bits + nn : U32), pb, lt(k1, nt)}

def es.kind(big: Bool, tok: A(), l: A(), w: W, +k: U32, +nt: U32,
  +bits: U32, +pb: Bool, +v: U32) -> ES:
  match big:
    case False{}:
      es.lit.b(tok, w, k, nt, bits, pb,
        get2(l, (CODE() + v : U32), (CLEN() + v : U32)))
    case True{}:
      +len = ((v >> 16n : U32) .&. 511 : U32)
      +dist = ((v .&. 65535 : U32) + 1 : U32)
      es.match.b(tok, w, k, nt, bits, pb, len, dist,
        get2(l, (len - 3 : U32), dslot(dist)))

def es.b(l: A(), w: W, +k: U32, +nt: U32, +bits: U32, +pb: Bool,
  pr: A() & U32) -> ES:
  (tok, +v) = pr
  es.kind(U32.is_ne((v .&. 2147483648 : U32), 0), tok, l, w, k, nt, bits,
    pb, v)

def es.loop(f: Nat, s: ES) -> ES:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case ES{tok, l, w, +k, +nt, +bits, pb, go}:
          match go:
            case False{}:
              ES{tok, l, w, k, nt, bits, pb, False{}}
            case True{}:
              es.loop(g, es.b(l, w, k, nt, bits, pb, get(tok, k)))

# ======================================================================
# Decoding. A 10-bit table resolves every code up to 10 bits in one
# lookup; longer ones are read one bit at a time the way zlib's puff.c
# does it: with count[len] and the symbols sorted by (len, sym), a code
# of length `len` is recognised by arithmetic alone.
#   [3200, 3520)  symbols sorted by (length, symbol)
#   [4096, 5120)  the 10-bit primary table
# The chunk array is in window form (`win`), so slot i holds bytes i..i+3 and
# any window of up to 25 bits starting in byte i is a single read.
# ======================================================================

def DSYM() -> U32:
  3200

# the 10-bit primary decode table: (sym << 8) | len, or 0 for "longer"
def PRI() -> U32:
  4096

def offs.b(+len: U32, r: R2) -> A():
  match r:
    case R2{l, +o, +c}:
      Array.set(U32, l, (NXT() + len : U32), (o + c : U32))

def offs(f: Nat, +len: U32, l: A()) -> A():
  match f:
    case 0n:
      l
    case 1n+g:
      offs(g, (len + 1 : U32), offs.b(len,
        get2(l, (NXT() + len - 1 : U32), (CNT() + len - 1 : U32))))

def sorted.b(+sym: U32, +len: U32, pr: A() & U32) -> A():
  (l, +i) = pr
  Array.set(U32, Array.set(U32, l, (NXT() + len : U32), (i + 1 : U32)),
    (DSYM() + i : U32), sym)

def sorted.sel(unused: Bool, +sym: U32, +len: U32, l: A()) -> A():
  match unused:
    case True{}:
      l
    case False{}:
      sorted.b(sym, len, get(l, (NXT() + len : U32)))

def sorted(ls: List<&2, U32>, +sym: U32, l: A()) -> A():
  match ls:
    case Nil{}:
      l
    case Con{+len, r}:
      sorted(r, (sym + 1 : U32), sorted.sel(U32.is_eq(len, 0), sym, len, l))

type PF is Type:
  PF{l: Array<U32>, at: U32, e: U32}

def pf.loop(f: Nat, s: PF) -> PF:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case PF{l, +at, +e}:
          pf.loop(g, PF{Array.set(U32, l, at, e), (at + 1 : U32), e})

def pf.fin(s: PF) -> A():
  match s:
    case PF{l, at, e}:
      l

def prim.b(+sym: U32, +len: U32, pr: A() & U32) -> A():
  (l, +code) = pr
  +free = (10 - len : U32)
  pf.fin(pf.loop(U32.to_nat(shl(1, free)), PF{l, (PRI() + shl(code, free) : U32),
    ((sym << 8n : U32) .|. len : U32)}))

def prim.sel(short: Bool, +sym: U32, +len: U32, l: A()) -> A():
  match short:
    case False{}:
      l
    case True{}:
      prim.b(sym, len, get(l, (CODE() + sym : U32)))

def prim(ls: List<&2, U32>, +sym: U32, l: A()) -> A():
  match ls:
    case Nil{}:
      l
    case Con{+len, r}:
      prim(r, (sym + 1 : U32), prim.sel(Bool.and(lt(0, len), U32.is_le(len, 10)),
        sym, len, l))

def dtable(+ls: List<&2, U32>) -> A():
  prim(ls, 0, sorted(ls, 0, offs(40n, 1, canon(ls, tables()))))

# ------------------------------------------------ one bit, one symbol

# bit `pos` of the stream, from the packed word of byte pos >> 3
def bit_at(+pos: U32, +word: U32) -> U32:
  (shr(word, (31 - (pos .&. 7 : U32) : U32)) .&. 1 : U32)

# the n (<= 25) bits at `pos`, from the packed word of byte pos >> 3
def peek(+word: U32, +pos: U32, +n: U32) -> U32:
  Bool.pick(U32, U32.is_eq(n, 0), 0,
    shr(shl(word, (pos .&. 7 : U32)), ((32 - n : U32) .&. 31 : U32)))

type SD is Type:
  SD{p: Array<U32>, l: Array<U32>, spos: U32, code: U32, first: U32,
    index: U32, len: U32, sym: U32, go: Bool}

def sd.hit(p: A(), +spos: U32, +code: U32, +first: U32, +index: U32,
  +len: U32, pr: A() & U32) -> SD:
  (l, +sym) = pr
  SD{p, l, spos, code, first, index, len, sym, False{}}

def sd.sel(hit: Bool, p: A(), l: A(), +spos: U32, +code: U32, +first: U32,
  +index: U32, +len: U32, +count: U32) -> SD:
  match hit:
    case True{}:
      sd.hit(p, spos, code, first, index, len,
        get(l, (DSYM() + index + code - first : U32)))
    case False{}:
      SD{p, l, spos, (code << 1n : U32), ((first + count : U32) << 1n : U32),
        (index + count : U32), (len + 1 : U32), 0, True{}}

def sd.c(p: A(), +spos: U32, +code: U32, +first: U32, +index: U32,
  +len: U32, pr: A() & U32) -> SD:
  (l, +count) = pr
  sd.sel(lt((code - first : U32), count), p, l, (spos + 1 : U32), code,
    first, index, len, count)

def sd.b(l: A(), +spos: U32, +code: U32, +first: U32, +index: U32,
  +len: U32, pr: A() & U32) -> SD:
  (p, +byte) = pr
  sd.c(p, spos, (code .|. bit_at(spos, byte) : U32), first, index, len,
    get(l, (CNT() + len : U32)))

def sd.loop(f: Nat, s: SD) -> SD:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case SD{p, l, +spos, +code, +first, +index, +len, +sym, go}:
          match go:
            case False{}:
              SD{p, l, spos, code, first, index, len, sym, False{}}
            case True{}:
              sd.loop(g, sd.b(l, spos, code, first, index, len,
                get(p, (spos >> 3n : U32))))

def sym.c(hit: Bool, p: A(), l: A(), +spos: U32, +e: U32) -> SD:
  match hit:
    case True{}:
      SD{p, l, (spos + (e .&. 255 : U32) : U32), 0, 0, 0, 0, (e >> 8n : U32),
        False{}}
    case False{}:
      sd.loop(41n, SD{p, l, spos, 0, 0, 0, 1, 0, True{}})

def sym.b(p: A(), +spos: U32, pr: A() & U32) -> SD:
  (l, +e) = pr
  sym.c(U32.is_ne(e, 0), p, l, spos, e)

def sym.a(l: A(), +spos: U32, pr: A() & U32) -> SD:
  (p, +w) = pr
  sym.b(p, spos, get(l, (PRI() + peek(w, spos, 10) : U32)))

def symbol(p: A(), l: A(), +spos: U32) -> SD:
  sym.a(l, spos, get(p, (spos >> 3n : U32)))

# ------------------------------------------------ extra bits

# Exactly `n` (<= 13) bits, most significant first: one read.
type RB is Type:
  RB{p: Array<U32>, pos: U32, v: U32}

def rb.one(+pos: U32, +n: U32, pr: A() & U32) -> RB:
  (p, +w) = pr
  RB{p, (pos + n : U32), peek(w, pos, n)}

def read_bits(p: A(), +pos: U32, +n: U32) -> RB:
  rb.one(pos, n, get(p, (pos >> 3n : U32)))

# ------------------------------------------------ the output array
# Decoded bytes go straight into one array, already packed four per slot
# (little-endian, the I/O format), and LZ copies read back from it (`dist`
# never exceeds `opos`). Each byte is written once into a zeroed slot, so
# a write is an OR. `cap` counts slots; the last one is kept for the byte
# count. A chunk's decoded size is not stored, so the array doubles
# whenever fewer than 260 bytes (one maximal token) of room are left.

# byte j of a packed little-endian array, given the slot holding it
def byte_of(+word: U32, +j: U32) -> U32:
  (shr(word, ((j .&. 3 : U32) << 3n : U32)) .&. 255 : U32)

def sb.b(+opos: U32, +b: U32, pr: A() & U32) -> A():
  (out, +w) = pr
  Array.set(U32, out, (opos >> 2n : U32),
    (w .|. shl(b, ((opos .&. 3 : U32) << 3n : U32)) : U32))

def set_byte(out: A(), +opos: U32, +b: U32) -> A():
  sb.b(opos, b, get(out, (opos >> 2n : U32)))

type GC is Type:
  GC{src: Array<U32>, dst: Array<U32>, i: U32}

def gc.b(dst: A(), +i: U32, pr: A() & U32) -> GC:
  (src, +v) = pr
  GC{src, Array.set(U32, dst, i, v), (i + 1 : U32)}

def gc.loop(f: Nat, s: GC) -> GC:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case GC{src, dst, +i}:
          gc.loop(g, gc.b(dst, i, get(src, i)))

type GR is Type:
  GR{out: Array<U32>, cap: U32}

def gr.b(+cap: U32, s: GC) -> GR:
  match s:
    case GC{src, dst, i}:
      GR{dst, cap}

def grow(out: A(), +cap: U32) -> GR:
  +c2 = (cap << 1n : U32)
  gr.b(c2, gc.loop(U32.to_nat(cap), GC{out, Array.new(U32, depth(32n, 1n, c2), 0), 0}))

def ensure(need: Bool, out: A(), +cap: U32) -> GR:
  match need:
    case True{}:
      grow(out, cap)
    case False{}:
      GR{out, cap}

type CP is Type:
  CP{out: Array<U32>, opos: U32, dist: U32}

def cp.b(+opos: U32, +dist: U32, pr: A() & U32) -> CP:
  (out, +w) = pr
  CP{set_byte(out, opos, byte_of(w, (opos - dist : U32))), (opos + 1 : U32), dist}

def cp.loop(f: Nat, s: CP) -> CP:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case CP{out, +opos, +dist}:
          cp.loop(g, cp.b(opos, dist, get(out, ((opos - dist : U32) >> 2n : U32))))

# ------------------------------------------------ the token loop
# `p` is the chunk's own array: symbols are read from bit `spos`, extra
# bits from bit `xpos` (the symbol section ends at bit `end`).

type DS is Type:
  DS{p: Array<U32>, l: Array<U32>, out: Array<U32>, cap: U32, spos: U32,
    xpos: U32, opos: U32, end: U32, go: Bool}

def ds.fin(p: A(), l: A(), +cap: U32, +spos: U32, +xpos: U32, +end: U32,
  c: CP) -> DS:
  match c:
    case CP{out, +opos, dist}:
      DS{p, l, out, cap, spos, xpos, opos, end, lt(spos, end)}

def ds.d3(l: A(), out: A(), +cap: U32, +spos: U32, +opos: U32, +end: U32,
  +len: U32, +db: U32, rb: RB) -> DS:
  match rb:
    case RB{p, +xpos, +v}:
      ds.fin(p, l, cap, spos, xpos, end,
        cp.loop(U32.to_nat(len), CP{out, opos, (db + v : U32)}))

def ds.d2(p: A(), out: A(), +cap: U32, +spos: U32, +xpos: U32, +opos: U32,
  +end: U32, +len: U32, r: R2) -> DS:
  match r:
    case R2{l, +db, +de}:
      ds.d3(l, out, cap, spos, opos, end, len, db, read_bits(p, xpos, de))

def ds.d1(out: A(), +cap: U32, +xpos: U32, +opos: U32, +end: U32,
  +len: U32, sd: SD) -> DS:
  match sd:
    case SD{p, l, +spos, code, first, index, n, +sym, go}:
      +di = (sym - 285 : U32)
      ds.d2(p, out, cap, spos, xpos, opos, end, len,
        get2(l, (832 + di : U32), (864 + di : U32)))

def ds.l2(l: A(), out: A(), +cap: U32, +spos: U32, +opos: U32, +end: U32,
  +lb: U32, rb: RB) -> DS:
  match rb:
    case RB{p, +xpos, +v}:
      ds.d1(out, cap, xpos, opos, end, (lb + v : U32), symbol(p, l, spos))

def ds.l1(p: A(), out: A(), +cap: U32, +spos: U32, +xpos: U32, +opos: U32,
  +end: U32, r: R2) -> DS:
  match r:
    case R2{l, +lb, +le}:
      ds.l2(l, out, cap, spos, opos, end, lb, read_bits(p, xpos, le))

def ds.c(lit: Bool, p: A(), l: A(), out: A(), +cap: U32, +spos: U32,
  +xpos: U32, +opos: U32, +end: U32, +sym: U32) -> DS:
  match lit:
    case True{}:
      DS{p, l, set_byte(out, opos, sym), cap, spos, xpos,
        (opos + 1 : U32), end, lt(spos, end)}
    case False{}:
      +li = (sym - 256 : U32)
      ds.l1(p, out, cap, spos, xpos, opos, end,
        get2(l, (768 + li : U32), (800 + li : U32)))

def ds.b(out: A(), +cap: U32, +xpos: U32, +opos: U32, +end: U32,
  sd: SD) -> DS:
  match sd:
    case SD{p, l, +spos, code, first, index, len, +sym, go}:
      ds.c(lt(sym, 256), p, l, out, cap, spos, xpos, opos, end, sym)

def ds.room(p: A(), l: A(), +spos: U32, +xpos: U32, +opos: U32, +end: U32,
  g: GR) -> DS:
  match g:
    case GR{out, +cap}:
      ds.b(out, cap, xpos, opos, end, symbol(p, l, spos))

def ds.loop(f: Nat, s: DS) -> DS:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case DS{p, l, out, +cap, +spos, +xpos, +opos, +end, go}:
          match go:
            case False{}:
              DS{p, l, out, cap, spos, xpos, opos, end, False{}}
            case True{}:
              ds.loop(g, ds.room(p, l, spos, xpos, opos, end,
                ensure(U32.is_le(((cap - 1 : U32) << 2n : U32), (opos + 260 : U32)),
                  out, cap)))

# ======================================================================
# Huffman code lengths, on arrays.
#
# Live symbols are packed as keys (freq << 9) | sym, sorted once, and
# merged with the two-queue method: leaves are consumed in key order and
# internal nodes are created in nondecreasing weight order, so both
# queues stay sorted and each merge is two comparisons. `h` holds
#   [0, 1024)     keys: leaves 0..m-1, internal nodes m..2m-2
#   [1024, 2048)  parent of each node       [2048, 3072)  depth
#   [3072, 3392)  the code length of each symbol
# ======================================================================

def PAR() -> U32:
  1024

def DEP() -> U32:
  2048

def LEN() -> U32:
  3072

def key_le(a: U32, b: U32) -> Bool:
  U32.is_le(a, b)

def keys(fs: List<&2, U32>, +sym: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match fs:
    case Nil{}:
      acc
    case Con{+f, r}:
      keys(r, (sym + 1 : U32), Bool.pick(List<&2, U32>, U32.is_eq(f, 0), acc,
        Con{((f << 9n : U32) .|. sym : U32), acc}))

# Two never-used symbols (318, 319: real ones stop at 314) keep the tree
# from being a single leaf, as Huff.pad does for the reference builder.
def keys_pad.sel(few: Bool, ks: List<&2, U32>) -> List<&2, U32>:
  match few:
    case True{}:
      Con{830, Con{831, ks}}
    case False{}:
      ks

def keys_pad(+ks: List<&2, U32>) -> List<&2, U32>:
  keys_pad.sel(lt(U32.from_nat(List.length(&2, U32, ks)), 2), ks)

type MG is Type:
  MG{h: Array<U32>, i: U32, j: U32, k: U32, m: U32, a: U32, go: Bool}

# Which queue gives up its head: a leaf while any remain and it is no
# heavier than the oldest unconsumed internal node.
def mg.take(+i: U32, +j: U32, +k: U32, +m: U32, +ki: U32, +kj: U32) -> Bool:
  Bool.and(lt(i, m), Bool.or(Bool.not(lt(j, k)), U32.is_le(ki, kj)))

# First pick: remember its index in `a`.
def mg.first(+i: U32, +j: U32, +k: U32, +m: U32, r: R2) -> MG:
  match r:
    case R2{h, +ki, +kj}:
      +leaf = mg.take(i, j, k, m, ki, kj)
      MG{h, Bool.pick(U32, leaf, (i + 1 : U32), i),
        Bool.pick(U32, leaf, j, (j + 1 : U32)), k, m,
        Bool.pick(U32, leaf, i, j), True{}}

# Second pick: node k := a + b.
def mg.join.b(+k: U32, +m: U32, +i: U32, +j: U32, +a: U32, +b: U32,
  r: R2) -> MG:
  match r:
    case R2{h, +ka, +kb}:
      +k1 = (k + 1 : U32)
      MG{Array.set(U32, Array.set(U32, Array.set(U32, h, k,
          ((ka .&. 4294966784 : U32) + (kb .&. 4294966784 : U32) : U32)),
          (PAR() + a : U32), k), (PAR() + b : U32), k),
        i, j, k1, m, 0, lt(k1, ((m << 1n : U32) - 1 : U32))}

def mg.second(+i: U32, +j: U32, +k: U32, +m: U32, +a: U32, r: R2) -> MG:
  match r:
    case R2{h, +ki, +kj}:
      +leaf = mg.take(i, j, k, m, ki, kj)
      +b = Bool.pick(U32, leaf, i, j)
      mg.join.b(k, m, Bool.pick(U32, leaf, (i + 1 : U32), i),
        Bool.pick(U32, leaf, j, (j + 1 : U32)), a, b, get2(h, a, b))

def mg.step.b(+k: U32, +m: U32, s: MG) -> MG:
  match s:
    case MG{h, +i, +j, k0, m0, +a, go}:
      mg.second(i, j, k, m, a, get2(h, i, j))

def mg.step(s: MG) -> MG:
  match s:
    case MG{h, +i, +j, +k, +m, a, go}:
      mg.step.b(k, m, mg.first(i, j, k, m, get2(h, i, j)))

def mg.loop(f: Nat, s: MG) -> MG:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case MG{h, +i, +j, +k, +m, +a, go}:
          match go:
            case False{}:
              MG{h, i, j, k, m, a, False{}}
            case True{}:
              mg.loop(g, mg.step(MG{h, i, j, k, m, a, True{}}))

# depth[x] = depth[parent[x]] + 1, from the root (node 2m-2) down.
type DP is Type:
  DP{h: Array<U32>, x: U32, root: U32}

def dp.c(+x: U32, +root: U32, pr: A() & U32) -> DP:
  (h, +d) = pr
  DP{Array.set(U32, h, (DEP() + x : U32),
    Bool.pick(U32, U32.is_eq(x, root), 0, (d + 1 : U32))), (x - 1 : U32), root}

def dp.b(+x: U32, +root: U32, pr: A() & U32) -> DP:
  (h, +p) = pr
  dp.c(x, root, get(h, (DEP() + p : U32)))

def dp.loop(f: Nat, s: DP) -> DP:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case DP{h, +x, +root}:
          dp.loop(g, dp.b(x, root, get(h, (PAR() + x : U32))))

# len[sym] = depth of its leaf
def ln.b(+x: U32, r: R2) -> A():
  match r:
    case R2{h, +key, +d}:
      Array.set(U32, h, (LEN() + (key .&. 511 : U32) : U32), d)

def ln.loop(f: Nat, +x: U32, h: A()) -> A():
  match f:
    case 0n:
      h
    case 1n+g:
      ln.loop(g, (x + 1 : U32), ln.b(x, get2(h, x, (DEP() + x : U32))))

def slice_list(a: A(), +base: U32, +k: U32) -> List<&2, U32>:
  arr_list(U32.to_nat(k), (base + k : U32), get(a, (base + k - 1 : U32)), Nil{})

def lens.fin(+m: U32, s: DP) -> List<&2, U32>:
  match s:
    case DP{h, x, root}:
      slice_list(ln.loop(U32.to_nat(m), 0, h), LEN(), 320)

def lens.b(+m: U32, s: MG) -> List<&2, U32>:
  match s:
    case MG{h, i, j, k, m0, a, go}:
      +root = ((m << 1n : U32) - 2 : U32)
      lens.fin(m, dp.loop(U32.to_nat((root + 1 : U32)), DP{h, root, root}))

# The code length of each of the 320 symbols, from their frequencies.
def lengths(fs: List<&2, U32>) -> List<&2, U32>:
  +ks = List.sort(~U32, ~key_le, keys_pad(keys(fs, 0, Nil{})))
  +m = U32.from_nat(List.length(&2, U32, ks))
  lens.b(m, mg.loop(U32.to_nat(m), MG{put_list(ks, 0, Array.new(U32, 12n, 0)),
    0, m, m, m, 0, lt(m, ((m << 1n : U32) - 1 : U32))}))

def u32be(+x: U32, rest: List<&2, U32>) -> List<&2, U32>:
  Con{(x >> 24n : U32), Con{((x >> 16n : U32) .&. 255 : U32),
    Con{((x >> 8n : U32) .&. 255 : U32), Con{(x .&. 255 : U32), rest}}}}

def be32(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{+a, r1}:
      match r1:
        case Nil{}:
          0
        case Con{+b, r2}:
          match r2:
            case Nil{}:
              0
            case Con{+c, r3}:
              match r3:
                case Nil{}:
                  0
                case Con{+d, r4}:
                  ((a << 24n) .|. (b << 16n) .|. (c << 8n) .|. d : U32)

def pass_b(e: ES) -> ES:
  match e:
    case ES{tok, l, w, k, +nt, bits, pb, go}:
      es.loop(U32.to_nat(nt), ES{tok, l, w, 0, nt, bits, True{}, lt(0, nt)})

# ------------------------------------------------ one chunk, array in, array out
# Every chunk array holds one byte per slot and its byte count in the
# last slot, which is how the I/O effects hand them over and take them.

def arr_len.b(+size: U32, pr: A() & U32) -> A() & U32:
  (a, +n) = pr
  (a, n)

def arr_len.a(pr: A() & U32) -> A() & U32:
  (a, +size) = pr
  arr_len.b(size, get(a, (size - 1 : U32)))

# the array back, with its byte count
def arr_len(a: A()) -> A() & U32:
  arr_len.a(Array.size(U32, a))

# ------------------------------------------------ packed chunk arrays
# Chunks cross the I/O boundary packed four bytes per slot, little-endian
# -- exactly their bytes in memory -- so the C effects move them with
# pread/pwrite and no conversion, and the byte count sits in the last
# slot. Inside a task (so on every core at once) they are turned into
# the two working forms:
#   windows:  w[i] = bytes i..i+3 big-endian, for hashing, matching and
#             reading any bit window with one access (`win`);
#   bytes:    one byte per slot, as the encoder and decoder write them,
#             packed back up at the end (`pack_le`).

type WN is Type:
  WN{p: Array<U32>, w: Array<U32>, i: U32, v: U32}

def wn.b(w: A(), +i: U32, +v: U32, pr: A() & U32) -> WN:
  (p, +word) = pr
  +v4 = ((v << 8n : U32) .|. byte_of(word, (i + 3 : U32)) : U32)
  WN{p, Array.set(U32, w, i, v4), (i + 1 : U32), (v4 .&. 16777215 : U32)}

def wn.loop(f: Nat, s: WN) -> WN:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case WN{p, w, +i, +v}:
          wn.loop(g, wn.b(w, i, v, get(p, ((i + 3 : U32) >> 2n : U32))))

def wn.fin(s: WN) -> A():
  match s:
    case WN{p, w, i, v}:
      w

def win.b(+n: U32, pr: A() & U32) -> A():
  (p, +w0) = pr
  wn.fin(wn.loop(U32.to_nat(n), WN{p, Array.new(U32, depth(32n, 1n, (n + 4 : U32)), 0), 0,
    (((w0 .&. 255 : U32) << 16n : U32) .|. (((w0 >> 8n : U32) .&. 255 : U32) << 8n : U32)
      .|. ((w0 >> 16n : U32) .&. 255 : U32) : U32)}))

# the window form of a packed chunk of n bytes
def win(p: A(), +n: U32) -> A():
  win.b(n, get(p, 0))

type PL is Type:
  PL{src: Array<U32>, dst: Array<U32>, k: U32}

def pl.c(dst: A(), +k: U32, +b0: U32, +b1: U32, r: R2) -> PL:
  match r:
    case R2{src, +b2, +b3}:
      PL{src, Array.set(U32, dst, k, (b0 .|. (b1 << 8n) .|. (b2 << 16n)
        .|. (b3 << 24n) : U32)), (k + 1 : U32)}

def pl.b(dst: A(), +k: U32, r: R2) -> PL:
  match r:
    case R2{src, +b0, +b1}:
      +at = (k << 2n : U32)
      pl.c(dst, k, (b0 .&. 255 : U32), (b1 .&. 255 : U32),
        get2(src, (at + 2 : U32), (at + 3 : U32)))

def pl.loop(f: Nat, s: PL) -> PL:
  match f:
    case 0n:
      s
    case 1n+g:
      match s:
        case PL{src, dst, +k}:
          +at = (k << 2n : U32)
          pl.loop(g, pl.b(dst, k, get2(src, at, (at + 1 : U32))))

def pl.fin(+len: U32, +cap: U32, s: PL) -> A():
  match s:
    case PL{src, dst, k}:
      Array.set(U32, dst, (cap - 1 : U32), len)

# one-byte-per-slot `src` (first `len` bytes) packed little-endian
def pack_le(src: A(), +len: U32) -> A():
  +words = ((len + 3 : U32) >> 2n : U32)
  +d = depth(32n, 1n, (words + 1 : U32))
  pl.fin(len, U32.pow(2, d), pl.loop(U32.to_nat(words),
    PL{src, Array.new(U32, d, 0), 0}))

def bl.loop(f: Nat, +j: U32, pr: A() & U32, acc: List<&2, U32>) -> List<&2, U32>:
  match f:
    case 0n:
      acc
    case 1n+g:
      (p, +w) = pr
      bl.loop(g, (j - 1 : U32), get(p, ((j - 1 : U32) >> 2n : U32)),
        Con{byte_of(w, j), acc})

# the bytes of a packed chunk, as a list (for tests)
def bytes_list(p: A(), +len: U32) -> List<&2, U32>:
  bl.loop(U32.to_nat(len), (len - 1 : U32), get(p, ((len - 1 : U32) >> 2n : U32)), Nil{})

def tops(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      Con{(x >> 24n : U32), tops(r)}

def parse_chain(w: A(), +n: U32, +chain: Nat) -> PS:
  +d = depth(32n, 1n, n)
  ps.loop(U32.to_nat(n), chain, PS{w, Array.new(U32, 15n, 0), Array.new(U32, 15n, 0),
    Array.new(U32, d, 0), Array.new(U32, 9n, 0), tables(), n, 0, 0, lt(0, n)})

def parse_arr(w: A(), +n: U32) -> PS:
  parse_chain(w, n, CHAIN())

def ca.out(+cap: U32, +lens: List<&2, U32>, +bits: U32, w: W) -> A():
  match w:
    case W{out, acc, nacc, +opos}:
      pack_le(put_list(u32be((opos - 328 : U32), u32be(bits, lens)), 0, out), opos)

def ca.fin(+cap: U32, +lens: List<&2, U32>, e: ES) -> A():
  match e:
    case ES{tok, l, w, k, nt, +bits, pb, go}:
      ca.out(cap, lens, bits, flush(w))

def ca.c(+n: U32, s: PS) -> A():
  match s:
    case PS{w, head, prev, tok, freq, t, n0, pos, +nt, more}:
      +lens = lengths(to_list(freq, 320))
      +dep = Nat.max(10n, 1n+depth(32n, 1n, n))
      ca.fin(U32.pow(2, dep), lens, pass_b(es.loop(U32.to_nat(nt),
        ES{tok, canon(lens, t), W{Array.new(U32, dep, 0), 0, 0, 328},
          0, nt, 0, False{}, lt(0, nt)})))

def ca.b(pr: A() & U32) -> A():
  (p, +n) = pr
  ca.c(n, parse_arr(win(p, n), n))

# One chunk's bytes in, its container record out -- byte for byte the
# layout src/codec.bend's comp_chunk writes.
def compress_arr(w: A()) -> A():
  ca.b(arr_len(w))

# ------------------------------------------------ decoding a chunk

type SL is Type:
  SL{a: Array<U32>, xs: List<&2, U32>}

def sl.loop(f: Nat, +i: U32, pr: A() & U32, acc: List<&2, U32>) -> SL:
  match f:
    case 0n:
      (a, v) = pr
      SL{a, acc}
    case 1n+g:
      (a, +v) = pr
      sl.loop(g, (i - 1 : U32), get(a, (i - 2 : U32)), Con{v, acc})

# slots [base, base + k) as a list, keeping the array
def slice(a: A(), +base: U32, +k: U32) -> SL:
  sl.loop(U32.to_nat(k), (base + k : U32), get(a, (base + k - 1 : U32)), Nil{})

def da.fin(s: DS) -> A():
  match s:
    case DS{p, l, out, +cap, spos, xpos, +opos, end, go}:
      Array.set(U32, out, (cap - 1 : U32), opos)

def da.c(+n: U32, s: SL) -> A():
  match s:
    case SL{p, +h}:
      +hdr = tops(h)
      +nbits = be32(List.drop(&2, U32, hdr, 4n))
      +end = (2624 + nbits : U32)
      +dep = Nat.max(10n, depth(32n, 1n, n))
      da.fin(ds.loop(U32.to_nat(nbits), DS{p,
        dtable(List.drop(&2, U32, hdr, 8n)), Array.new(U32, dep, 0),
        U32.pow(2, dep), 2624, end, 0, end, lt(2624, end)}))

def da.b(pr: A() & U32) -> A():
  (p, +n) = pr
  da.c(n, slice(win(p, n), 0, 328))

# One chunk's container record in, its bytes out.
def decompress_arr(p: A()) -> A():
  da.b(arr_len(p))

# an empty packed array with room for `len` bytes and the count slot
def new_packed(+len: U32) -> A():
  Array.new(U32, depth(32n, 1n, ((len >> 2n : U32) + 2 : U32)), 0)

# store the byte count in the last slot
def pack_cap.b(+len: U32, pr: A() & U32) -> A():
  (a, +size) = pr
  Array.set(U32, a, (size - 1 : U32), len)

def pack_cap(a: A(), +len: U32) -> A():
  pack_cap.b(len, Array.size(U32, a))

# ------------------------------------------------ list adapters (tests)

# a list of bytes as a packed chunk array
def of_list(+xs: List<&2, U32>) -> A():
  +n = U32.from_nat(List.length(&2, U32, xs))
  pack_le(fill(xs, 0, Array.new(U32, depth(32n, 1n, (n + 1 : U32)), 0)), n)

def to_list.b(pr: A() & U32) -> List<&2, U32>:
  (a, +n) = pr
  bytes_list(a, n)

def compress_chunk(+xs: List<&2, U32>) -> List<&2, U32>:
  to_list.b(arr_len(compress_arr(of_list(xs))))

def decompress_chunk(+blob: List<&2, U32>) -> List<&2, U32>:
  to_list.b(arr_len(decompress_arr(of_list(blob))))

def parse.b(pr: A() & U32) -> PS:
  (p, +n) = pr
  parse_arr(win(p, n), n)

def parse(+xs: List<&2, U32>) -> PS:
  parse.b(arr_len(of_list(xs)))
