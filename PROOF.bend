import Base
import ./src/byte.bend as B
import ./src/bits.bend as Bits
import ./src/huff.bend as Huff
import ./src/lz.bend as LZ
import ./src/chunks.bend as Chunks
import ./src/codec.bend as Codec
import ./src/atree.bend as T
import ./LAWS.bend as Laws

# Proofs of the claims in LAWS.bend. `bend PROOF.bend` is the gate: it
# prints "All terms check." only when every law here is closed.

# Two motives for refuting a clash. `Absurd(G, Some{v})` computes to the
# goal G, so rewriting the impossible hypothesis into `None{}` turns the
# goal into `Unit` and `Unit{}` closes it.
def Absurd(G: Type, m: Maybe<&2, B.Sym>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      G

def AbsurdB(G: Type, b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# ------------------------------------------------------- 0. groundwork

def Laws.take_drop(A, xs, n):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          %Laws.take_drop(A, t, p) : {Con{h, List.append(&2, A,
            List.take(&2, A, t, p),
            List.drop(&2, A, t, p))} == Con{h, _} : List<&2, A>}
          {==}

def Laws.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# ------------------------------------------------ 1. the octet boundary

# All 256 bytes, each closed by computation: `to_u32` builds the word out
# of eight known bits and `from_u32` takes them straight back out.
def Laws.byte_roundtrip(x):
  match x:
    case B.Byte{False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, False{}, True{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, False{}, True{}, True{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, False{}, True{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{False{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, False{}, True{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, False{}, True{}, True{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, False{}, True{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, False{}, True{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, False{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, False{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, False{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, False{}, True{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}}:
      {==}
    case B.Byte{True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}}:
      {==}

def Laws.octets_roundtrip(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{y, t}:
      %Laws.octets_roundtrip(t) : {Con{B.from_u32(B.to_u32(y)),
        B.decode(B.encode(t))} == Con{y, _} : B.Bytes()}
      %Laws.byte_roundtrip(y) : {Con{B.from_u32(B.to_u32(y)),
        B.decode(B.encode(t))} == Con{_, B.decode(B.encode(t))} : B.Bytes()}
      {==}

# ---------------------------------------------------- 2. the bit layer

# `pack`, `padding` and `unpack` share one case structure, so eight of
# the nine cases are pure computation and only the full-byte case needs
# the induction hypothesis.
def Laws.bits_roundtrip(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b0, r0}:
      match r0:
        case Nil{}:
          {==}
        case Con{b1, r1}:
          match r1:
            case Nil{}:
              {==}
            case Con{b2, r2}:
              match r2:
                case Nil{}:
                  {==}
                case Con{b3, r3}:
                  match r3:
                    case Nil{}:
                      {==}
                    case Con{b4, r4}:
                      match r4:
                        case Nil{}:
                          {==}
                        case Con{b5, r5}:
                          match r5:
                            case Nil{}:
                              {==}
                            case Con{b6, r6}:
                              match r6:
                                case Nil{}:
                                  {==}
                                case Con{b7, r7}:
                                  %Laws.bits_roundtrip(r7) : {Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, Bits.unpack(Bits.pack(r7))}}}}}}}} ==
                                    Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, _}}}}}}}} : B.Bits()}
                                  {==}

# ------------------------------------------------- 3. the chunk header

def Laws.lens_roundtrip(ls, rest):
  match ls:
    case Nil{}:
      {==}
    case Con{y, t}:
      match y:
        case B.Byte{b0, b1, b2, b3, b4, b5, b6, b7}:
          Equal.cong(B.Bytes() & B.Bits(), B.Bytes() & B.Bits(),
            r => Huff.lens_read.put(B.Byte{b0, b1, b2, b3, b4, b5, b6, b7}, r),
            Huff.lens_read(List.length(&2, B.Byte, t),
              List.append(&2, Bool, Huff.lens_write(t), rest)),
            (t, rest),
            Laws.lens_roundtrip(t, rest))


# --------------------------------------------------------- 5. chunking

def Laws.chunks_roundtrip(A, d, n, xs):
  match d:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(List<&2, A>,
        Chunks.join(A, Chunks.of_n(A, k, Nat.div(n, 2n),
          List.take(&2, A, xs, Nat.div(n, 2n)))),
        List.take(&2, A, xs, Nat.div(n, 2n)),
        Laws.chunks_roundtrip(A, k, Nat.div(n, 2n),
          List.take(&2, A, xs, Nat.div(n, 2n))))
        : {List.append(&2, A, _, Chunks.join(A, Chunks.of_n(A, k,
            Nat.sub(n, Nat.div(n, 2n)),
            List.drop(&2, A, xs, Nat.div(n, 2n))))) == xs : List<&2, A>}
      %Equal.sym(List<&2, A>,
        Chunks.join(A, Chunks.of_n(A, k, Nat.sub(n, Nat.div(n, 2n)),
          List.drop(&2, A, xs, Nat.div(n, 2n)))),
        List.drop(&2, A, xs, Nat.div(n, 2n)),
        Laws.chunks_roundtrip(A, k, Nat.sub(n, Nat.div(n, 2n)),
          List.drop(&2, A, xs, Nat.div(n, 2n))))
        : {List.append(&2, A,
            List.take(&2, A, xs, Nat.div(n, 2n)), _) == xs : List<&2, A>}
      Laws.take_drop(A, xs, Nat.div(n, 2n))

# ------------------------------------------------------ 6. parallelism

# The parallel let is a let: both sides of the equation are the same
# term once the two hypotheses are in place.
def Laws.chunks_par(c):
  match c:
    case Chunks.CLeaf{+xs}:
      {==}
    case Chunks.CNode{+lo, +hi}:
      %Laws.chunks_par(lo) : {Chunks.CNode{
        Chunks.pmap(~U32, ~U32, ~Codec.comp_oct, lo),
        Chunks.pmap(~U32, ~U32, ~Codec.comp_oct, hi)} == Chunks.CNode{_,
        Chunks.smap(~U32, ~U32, ~Codec.comp_oct, hi)} : Chunks.Chunks<U32>}
      %Laws.chunks_par(hi) : {Chunks.CNode{
        Chunks.pmap(~U32, ~U32, ~Codec.comp_oct, lo),
        Chunks.pmap(~U32, ~U32, ~Codec.comp_oct, hi)} == Chunks.CNode{
        Chunks.pmap(~U32, ~U32, ~Codec.comp_oct, lo), _} : Chunks.Chunks<U32>}
      {==}

def Laws.chunks_par_dec(c):
  match c:
    case Chunks.CLeaf{+xs}:
      {==}
    case Chunks.CNode{+lo, +hi}:
      %Laws.chunks_par_dec(lo) : {Chunks.CNode{
        Chunks.pmap(~B.Byte, ~U32, ~Codec.decomp_oct, lo),
        Chunks.pmap(~B.Byte, ~U32, ~Codec.decomp_oct, hi)} == Chunks.CNode{_,
        Chunks.smap(~B.Byte, ~U32, ~Codec.decomp_oct, hi)} : Chunks.Chunks<U32>}
      %Laws.chunks_par_dec(hi) : {Chunks.CNode{
        Chunks.pmap(~B.Byte, ~U32, ~Codec.decomp_oct, lo),
        Chunks.pmap(~B.Byte, ~U32, ~Codec.decomp_oct, hi)} == Chunks.CNode{
        Chunks.pmap(~B.Byte, ~U32, ~Codec.decomp_oct, lo), _} : Chunks.Chunks<U32>}
      {==}

def Laws.fast_par(t):
  match t:
    case T.ALf{a}:
      {==}
    case T.ANd{lo, hi}:
      %Laws.fast_par(lo) : {T.ANd{T.tcomp(lo), T.tcomp(hi)} ==
        T.ANd{_, T.tcomp_seq(hi)} : T.AT}
      %Laws.fast_par(hi) : {T.ANd{T.tcomp(lo), T.tcomp(hi)} ==
        T.ANd{T.tcomp(lo), _} : T.AT}
      {==}

def Laws.fast_par_dec(t):
  match t:
    case T.ALf{a}:
      {==}
    case T.ANd{lo, hi}:
      %Laws.fast_par_dec(lo) : {T.ANd{T.tdec(lo), T.tdec(hi)} ==
        T.ANd{_, T.tdec_seq(hi)} : T.AT}
      %Laws.fast_par_dec(hi) : {T.ANd{T.tdec(lo), T.tdec(hi)} ==
        T.ANd{T.tdec(lo), _} : T.AT}
      {==}

# --------------------------------------------- 7. back-references

def Laws.lz_copy_len(l, d, h):
  match l:
    case 0n:
      {==}
    case 1n+k:
      %Laws.add_succ(k, List.length(&2, B.Byte, h))
        : {List.length(&2, B.Byte, LZ.copy(k, d, Con{LZ.back(h, d), h}))
            == _ : Nat}
      Laws.lz_copy_len(k, d, Con{LZ.back(h, d), h})

def Laws.lz_lits(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{b, t}:
      Laws.lz_lits(t, Con{b, h})

# --------------------------------------- 4. the prefix-code property

# Induction on the path. Four of the six shapes per branch are
# impossible -- the hypothesis says the path lands on a leaf, so it can
# neither run out early nor run on past one -- and each is closed by
# rewriting that hypothesis into `None{}` through the `Absurd` motive.
def Laws.huff_walk(root, p, cur, rest, s, ne, at):
  match p:
    case Nil{}:
      %ne : AbsurdB({Huff.decode(List.append(&2, Bool, Nil{}, rest), root, cur) ==
          Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
        _)
      Unit{}
    case Con{b, q}:
      match b:
        case False{}:
          match q:
            case Nil{}:
              match cur:
                case Huff.HLeaf{k0}:
                  %at : Absurd({Huff.decode(List.append(&2, Bool, Con{False{}, Nil{}}, rest), root, Huff.HLeaf{k0}) ==
                      Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                    _)
                  Unit{}
                case Huff.HNode{lo, hi}:
                  match lo:
                    case Huff.HLeaf{k1}:
                      %Equal.cong(Maybe<&2, B.Sym>, B.Sym,
                        m => Maybe.default(&2, B.Sym, m, k1),
                        Some{k1}, Some{s}, at)
                        : {Con{k1, Huff.decode(rest, root, root)} ==
                          Con{_, Huff.decode(rest, root, root)}
                          : List<&2, B.Sym>}
                      {==}
                    case Huff.HNode{a, c}:
                      %at : Absurd({Huff.decode(List.append(&2, Bool, Con{False{}, Nil{}}, rest), root, Huff.HNode{Huff.HNode{a, c}, hi}) ==
                          Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                        _)
                      Unit{}
            case Con{b2, q2}:
              match cur:
                case Huff.HLeaf{k0}:
                  %at : Absurd({Huff.decode(List.append(&2, Bool, Con{False{}, Con{b2, q2}}, rest), root, Huff.HLeaf{k0}) ==
                      Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                    _)
                  Unit{}
                case Huff.HNode{lo, hi}:
                  match lo:
                    case Huff.HLeaf{k1}:
                      %at : Absurd({Huff.decode(List.append(&2, Bool, Con{False{}, Con{b2, q2}}, rest), root, Huff.HNode{Huff.HLeaf{k1}, hi}) ==
                          Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                        _)
                      Unit{}
                    case Huff.HNode{a, c}:
                      Laws.huff_walk(root, Con{b2, q2},
                        Huff.HNode{a, c}, rest, s, {==}, at)
        case True{}:
          match q:
            case Nil{}:
              match cur:
                case Huff.HLeaf{k0}:
                  %at : Absurd({Huff.decode(List.append(&2, Bool, Con{True{}, Nil{}}, rest), root, Huff.HLeaf{k0}) ==
                      Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                    _)
                  Unit{}
                case Huff.HNode{lo, hi}:
                  match hi:
                    case Huff.HLeaf{k1}:
                      %Equal.cong(Maybe<&2, B.Sym>, B.Sym,
                        m => Maybe.default(&2, B.Sym, m, k1),
                        Some{k1}, Some{s}, at)
                        : {Con{k1, Huff.decode(rest, root, root)} ==
                          Con{_, Huff.decode(rest, root, root)}
                          : List<&2, B.Sym>}
                      {==}
                    case Huff.HNode{a, c}:
                      %at : Absurd({Huff.decode(List.append(&2, Bool, Con{True{}, Nil{}}, rest), root, Huff.HNode{lo, Huff.HNode{a, c}}) ==
                          Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                        _)
                      Unit{}
            case Con{b2, q2}:
              match cur:
                case Huff.HLeaf{k0}:
                  %at : Absurd({Huff.decode(List.append(&2, Bool, Con{True{}, Con{b2, q2}}, rest), root, Huff.HLeaf{k0}) ==
                      Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                    _)
                  Unit{}
                case Huff.HNode{lo, hi}:
                  match hi:
                    case Huff.HLeaf{k1}:
                      %at : Absurd({Huff.decode(List.append(&2, Bool, Con{True{}, Con{b2, q2}}, rest), root, Huff.HNode{lo, Huff.HLeaf{k1}}) ==
                          Con{s, Huff.decode(rest, root, root)} : List<&2, B.Sym>},
                        _)
                      Unit{}
                    case Huff.HNode{a, c}:
                      Laws.huff_walk(root, Con{b2, q2},
                        Huff.HNode{a, c}, rest, s, {==}, at)
