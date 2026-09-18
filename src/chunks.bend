import Base

# A balanced binary tree of chunks. Splitting by depth (rather than by a
# fixed chunk size) gives exactly 2^d leaves of near-equal length, which
# is what Bend's fork-join scheduler wants: both sides of every parallel
# call carry the same amount of work. (It also needs enough of them: the
# scheduler only fans out across all cores from roughly 2^8 leaves.)
#
# Generic in the element type, so the input can be split as raw octets
# and each chunk turned into bytes inside its own parallel task.
type Chunks<-A: Data> is Data:
  CLeaf{items: List<&2, A>}
  CNode{lo: Chunks<A>, hi: Chunks<A>}

# The split, given the list's length `n`: the length is measured once at
# the top and halved on the way down, rather than re-counted at every
# node. The cut position does not matter for correctness -- take and drop
# partition the list wherever they cut -- which is why `chunks_roundtrip`
# holds for every `n`, not only the true length.
def of_n(-A: Data, +d: Nat, +n: Nat, +xs: List<&2, A>) -> Chunks<A>:
  match d:
    case 0n:
      CLeaf{xs}
    case 1n+k:
      +h = Nat.div(n, 2n)
      a b = of_n(A, k, h, List.take(&2, A, xs, h)) of_n(A, k, Nat.sub(n, h), List.drop(&2, A, xs, h))
      CNode{a, b}

def of(-A: Data, +d: Nat, +xs: List<&2, A>) -> Chunks<A>:
  of_n(A, d, List.length(&2, A, xs), xs)

def of_list(-A: Data, +d: Nat, +xs: List<&2, List<&2, A>>) -> Chunks<A>:
  match d:
    case 0n:
      CLeaf{Maybe.default(&2, List<&2, A>, List.head(&2, List<&2, A>, xs), Nil{})}
    case 1n+k:
      +h = Nat.div(List.length(&2, List<&2, A>, xs), 2n)
      CNode{of_list(A, k, List.take(&2, List<&2, A>, xs, h)),
        of_list(A, k, List.drop(&2, List<&2, A>, xs, h))}

def join(-A: Data, c: Chunks<A>) -> List<&2, A>:
  match c:
    case CLeaf{xs}:
      xs
    case CNode{lo, hi}:
      a b = join(A, lo) join(A, hi)
      List.append(&2, A, a, b)

# The two maps differ only in the parallel call: `a b = f(x) g(y)` hands
# the two halves to two lanes. Bend is pure and affine, so this cannot
# change the result -- `chunks_par` in LAWS.bend states exactly that.
def smap(~A: Data, ~B: Data, ~f: @+x: List<&2, A> -> List<&2, B>,
  +c: Chunks<A>) -> Chunks<B>:
  match c:
    case CLeaf{+xs}:
      CLeaf{f(xs)}
    case CNode{lo, hi}:
      CNode{smap(~A, ~B, ~f, lo), smap(~A, ~B, ~f, hi)}

def pmap(~A: Data, ~B: Data, ~f: @+x: List<&2, A> -> List<&2, B>,
  +c: Chunks<A>) -> Chunks<B>:
  match c:
    case CLeaf{+xs}:
      CLeaf{f(xs)}
    case CNode{lo, hi}:
      a b = pmap(~A, ~B, ~f, lo) pmap(~A, ~B, ~f, hi)
      CNode{a, b}

# The leaves, left to right, as a list of lists.
def leaves(-A: Data, c: Chunks<A>, acc: List<&2, List<&2, A>>) ->
  List<&2, List<&2, A>>:
  match c:
    case CLeaf{xs}:
      Con{xs, acc}
    case CNode{lo, hi}:
      leaves(A, lo, leaves(A, hi, acc))
