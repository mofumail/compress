import Base
import ./src/byte.bend as B
import ./src/bits.bend as Bits
import ./src/huff.bend as Huff
import ./src/lz.bend as LZ
import ./src/chunks.bend as Chunks
import ./src/codec.bend as Codec
import ./src/atree.bend as T

# =====================================================================
# What this codec promises
# =====================================================================
#
# The pipeline is a stack of four encodings, each with an inverse:
#
#   octets -> chunks -> LZ77 tokens -> Huffman symbols -> bits -> octets
#
# A law per layer says that layer loses nothing. Composed, they say the
# container is lossless for any token stream the parser can emit.
#
# Two things are NOT claimed here, and OPEN.bend states them formally:
#   - that the match finder only emits references the decoder can
#     follow (`lz_copy_len` pins down what a reference expands to, so it
#     can never desynchronise the stream; the rest is tested), and
#   - that the fast ring-buffer decoder the binary runs agrees with the
#     reference `LZ.expand` these laws are about (differential test in
#     test/decode_test.bend).

# ---------------------------------------------------------------------
# 0. Groundwork: taking and dropping a prefix partitions a list.
# ---------------------------------------------------------------------

law take_drop:
  for -A: Data
  for xs: List<&2, A>
  for n: Nat
  {List.append(&2, A, List.take(&2, A, xs, n),
    List.drop(&2, A, xs, n)) == xs : List<&2, A>}

law add_succ:
  for a: Nat
  for b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

# ---------------------------------------------------------------------
# 1. The octet boundary. A byte is eight bits here and one machine word
#    at the edge; going out and back is the identity, for all 256.
# ---------------------------------------------------------------------

law byte_roundtrip:
  for x: B.Byte
  {B.from_u32(B.to_u32(x)) == x : B.Byte}

law octets_roundtrip:
  for xs: B.Bytes()
  {B.decode(B.encode(xs)) == xs : B.Bytes()}

# ---------------------------------------------------------------------
# 2. The bit layer. Packing pads the final byte with zeros, and
#    `padding` names exactly that padding -- so unpacking recovers the
#    bit stream on the nose, not merely as a prefix.
# ---------------------------------------------------------------------

law bits_roundtrip:
  for bs: B.Bits()
  {Bits.unpack(Bits.pack(bs)) ==
    List.append(&2, Bool, bs, Bits.padding(bs)) : B.Bits()}

# ---------------------------------------------------------------------
# 3. The chunk header. Both sides rebuild the tree from this table with
#    the same `canon`, so the decoder's tree is the encoder's tree by
#    construction; all the header has to do is survive the trip, with
#    whatever follows it left untouched.
# ---------------------------------------------------------------------

law lens_roundtrip:
  for ls: B.Bytes()
  for rest: B.Bits()
  {Huff.lens_read(List.length(&2, B.Byte, ls),
    List.append(&2, Bool, Huff.lens_write(ls), rest)) ==
    (ls, rest) : B.Bytes() & B.Bits()}

# ---------------------------------------------------------------------
# 4. The prefix-code property -- the heart of Huffman.
#
#    If a non-empty path lands on the symbol `s` in the subtree `cur`,
#    then reading that path off the front of the stream yields `s` and
#    leaves the remainder exactly as it was. Nothing about the tree's
#    shape is assumed: this is what makes any tree a valid code.
# ---------------------------------------------------------------------

law huff_walk:
  for +root: Huff.HTree
  for +p: B.Bits()
  for cur: Huff.HTree
  for rest: B.Bits()
  for s: B.Sym
  for ne: {List.is_empty(&2, Bool, p) == False{} : Bool}
  for at: {Huff.at(cur, p) == Some{s} : Maybe<&2, B.Sym>}
  {Huff.decode(List.append(&2, Bool, p, rest), root, cur) ==
    Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>}

# ---------------------------------------------------------------------
# 5. Chunking. Splitting to depth `d` and concatenating the leaves back
#    is the identity -- for any element type, and for any length hint
#    `n`, true or not: the hint only moves where take and drop cut, and
#    they partition the list wherever they cut. `Chunks.of` passes the
#    true length, so ragged and empty chunks are covered too.
# ---------------------------------------------------------------------

law chunks_roundtrip:
  for -A: Data
  for +d: Nat
  for +n: Nat
  for +xs: List<&2, A>
  {Chunks.join(A, Chunks.of_n(A, d, n, xs)) == xs : List<&2, A>}

# ---------------------------------------------------------------------
# 6. Parallelism is not an optimisation with caveats: the parallel map
#    and the sequential map are the same function, for the exact per-
#    chunk work each direction runs. This is the law that makes the
#    16-core run trustworthy.
# ---------------------------------------------------------------------

law chunks_par:
  for +c: Chunks.Chunks<U32>
  {Chunks.pmap(~U32, ~U32, ~Codec.comp_oct, c) ==
    Chunks.smap(~U32, ~U32, ~Codec.comp_oct, c) : Chunks.Chunks<U32>}

law chunks_par_dec:
  for +c: Chunks.Chunks<B.Byte>
  {Chunks.pmap(~B.Byte, ~U32, ~Codec.decomp_oct, c) ==
    Chunks.smap(~B.Byte, ~U32, ~Codec.decomp_oct, c) : Chunks.Chunks<U32>}

# The fast path (src/fast.bend, what the binary runs) maps over its own
# tree of chunk arrays; the same guarantee holds there.

law fast_par:
  for t: T.AT
  {T.tcomp(t) == T.tcomp_seq(t) : T.AT}

law fast_par_dec:
  for t: T.AT
  {T.tdec(t) == T.tdec_seq(t) : T.AT}

# ---------------------------------------------------------------------
# 7. Back-references. A `Ref{d, l}` emits exactly `l` bytes, whatever
#    `d` is -- including `d < l`, where the copy reads back bytes this
#    very loop just wrote. That is what keeps encoder and decoder in
#    step: no reference can ever shift the output by an unintended
#    amount.
# ---------------------------------------------------------------------

law lz_copy_len:
  for +l: Nat
  for +d: Nat
  for +h: B.Bytes()
  {List.length(&2, B.Byte, LZ.copy(l, d, h)) ==
    Nat.add(l, List.length(&2, B.Byte, h)) : Nat}

# A token stream of literals expands to precisely those literals: the
# base case of the decoder, with no reference involved.

law lz_lits:
  for xs: B.Bytes()
  for h: B.Bytes()
  {LZ.expand(LZ.lits(xs), h) ==
    List.reverse.go(&2, B.Byte, xs, h) : B.Bytes()}
