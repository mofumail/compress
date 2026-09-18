import Base
import ./fast.bend as F

# The fast path's chunk tree: chunks travel as arrays (see
# ffi/read_arrays.c), are paired up into a balanced tree, mapped over in
# parallel, and written back from the leaves. Arrays are affine, so the
# tree is built by pairing neighbours rather than by measuring and
# splitting a list (which would need to read it twice).

type AT is Type:
  ALf{a: Array<U32>}
  ANd{lo: AT, hi: AT}

def Arrs() -> Type:
  List<&1, Array<U32>>

def wrap(xs: Arrs()) -> List<&1, AT>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, r}:
      Con{ALf{a}, wrap(r)}

def pairs(xs: List<&1, AT>) -> List<&1, AT>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, r}:
      match r:
        case Nil{}:
          Con{a, Nil{}}
        case Con{b, rr}:
          Con{ANd{a, b}, pairs(rr)}

# Pair neighbours until one tree is left: balanced for 2^d leaves, and
# the leaves keep their order.
def collapse(f: Nat, xs: List<&1, AT>) -> AT:
  match f:
    case 0n:
      ALf{Array.new(U32, 1n, 0)}
    case 1n+g:
      match xs:
        case Nil{}:
          ALf{Array.new(U32, 1n, 0)}
        case Con{a, r}:
          match r:
            case Nil{}:
              a
            case Con{b, rr}:
              collapse(g, pairs(Con{a, Con{b, rr}}))

def leaves(t: AT, acc: Arrs()) -> Arrs():
  match t:
    case ALf{a}:
      Con{a, acc}
    case ANd{lo, hi}:
      leaves(lo, leaves(hi, acc))

def tcomp(t: AT) -> AT:
  match t:
    case ALf{a}:
      ALf{F.compress_arr(a)}
    case ANd{lo, hi}:
      x y = tcomp(lo) tcomp(hi)
      ANd{x, y}

def tcomp_seq(t: AT) -> AT:
  match t:
    case ALf{a}:
      ALf{F.compress_arr(a)}
    case ANd{lo, hi}:
      ANd{tcomp_seq(lo), tcomp_seq(hi)}

def tdec(t: AT) -> AT:
  match t:
    case ALf{a}:
      ALf{F.decompress_arr(a)}
    case ANd{lo, hi}:
      x y = tdec(lo) tdec(hi)
      ANd{x, y}

def tdec_seq(t: AT) -> AT:
  match t:
    case ALf{a}:
      ALf{F.decompress_arr(a)}
    case ANd{lo, hi}:
      ANd{tdec_seq(lo), tdec_seq(hi)}

def pick_comp(par: Bool, t: AT) -> AT:
  match par:
    case True{}:
      tcomp(t)
    case False{}:
      tcomp_seq(t)

def pick_dec(par: Bool, t: AT) -> AT:
  match par:
    case True{}:
      tdec(t)
    case False{}:
      tdec_seq(t)

