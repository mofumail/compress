import Base
import ./byte.bend as B

# A fixed-depth binary trie keyed by a bit path. Unlike `Array` it is
# Data-kinded, so a table can be shared freely across the parallel
# workers instead of being threaded through them one owner at a time.
type Tab<a, -A: Kind(a)> is Kind(a):
  TLeaf{val: A}
  TNode{lo: Tab<a, A>, hi: Tab<a, A>}

def new(-A: Data, +d: Nat, +v: A) -> Tab<&2, A>:
  match d:
    case 0n:
      TLeaf{v}
    case 1n+p:
      TNode{new(A, p, v), new(A, p, v)}

def get(-A: Data, t: Tab<&2, A>, k: B.Bits()) -> A:
  match t:
    case TLeaf{v}:
      v
    case TNode{lo, hi}:
      match k:
        case Nil{}:
          get(A, lo, Nil{})
        case Con{b, r}:
          match b:
            case False{}:
              get(A, lo, r)
            case True{}:
              get(A, hi, r)

def set(-A: Data, t: Tab<&2, A>, k: B.Bits(), +v: A) -> Tab<&2, A>:
  match t:
    case TLeaf{old}:
      TLeaf{v}
    case TNode{lo, hi}:
      match k:
        case Nil{}:
          TNode{set(A, lo, Nil{}, v), hi}
        case Con{b, r}:
          match b:
            case False{}:
              TNode{set(A, lo, r, v), hi}
            case True{}:
              TNode{lo, set(A, hi, r, v)}

# Every leaf, left to right: the table read back as a list.
def list(-A: Data, t: Tab<&2, A>) -> List<&2, A>:
  match t:
    case TLeaf{v}:
      [v]
    case TNode{lo, hi}:
      List.append(&2, A, list(A, lo), list(A, hi))
