import Base
import ./src/byte.bend as B
import ./src/lz.bend as LZ
import ./src/codec.bend as Codec
import ./src/fast.bend as F

# Claims this project relies on but has NOT proven. They are kept out of
# LAWS.bend so that `bend PROOF.bend` stays an honest gate; `bend
# OPEN.bend` reports them as open (TODOs), which is what they are.
# Each is covered by a test instead, named beside it.

# The greedy parser only emits references the decoder can follow, so
# the LZ layer as a whole is lossless.
# Proof sketch: `lcp_of` certifies w[p-d+i] == w[p+i] for i < l, and
# `back(rev(take(p, w)), d) == w[p-d]` for d <= p; induction on l.
# The missing piece is that index lemma about get/reverse/take.
# Tested by: test/lz_test.bend, test/decode_test.bend, bench.sh (cmp).
law lz_roundtrip:
  for +w: B.Bytes()
  {LZ.expand_all(LZ.parse_all(w)) == w : B.Bytes()}

# The ring-buffer decoder the binary runs agrees with the reference
# decoder that LAWS.bend reasons about, on every stream `parse_all` emits.
# Tested by: test/decode_test.bend (differential, 200 KB real text).
law fast_decoder:
  for +w: B.Bytes()
  {LZ.expand_fast_all(LZ.parse_all(w)) == LZ.expand_all(LZ.parse_all(w)) : B.Bytes()}

# The fast codec (src/fast.bend), which the binary runs, round-trips...
# Tested by: test/fast_test.bend, bench.sh (cmp on every run).
law fast_roundtrip:
  for +xs: List<&2, U32>
  {F.decompress_chunk(F.compress_chunk(xs)) == xs : List<&2, U32>}

# ...and writes exactly the format of the proven reference codec: its
# chunks decode, under the reference decoder, to the input.
# Tested by: test/fast_test.bend (both directions), and whole files with
# BZ_MODE=12 on the fast path's output.
law fast_is_reference_format:
  for +xs: List<&2, U32>
  {Codec.decomp_chunk(B.decode(F.compress_chunk(xs))) == B.decode(xs) : B.Bytes()}
