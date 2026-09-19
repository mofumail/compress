import Base
import ../src/fast.bend as F
import ../src/raw.bend as Raw

# Profiling the fast codec on one core: each P runs one more stage than
# the last over the same chunks, so differences are per-stage costs.
#   P=0 read only   1 +parse   2 +Huffman lengths   3 whole compress
#   P=4 decompress (BZ_IN must then be a .bz file)

def Arrs() -> Type:
  List<&1, Array<U32>>

def ra.fin(fr: File & Result<&1, &1, U32 & String, Arrs()>) -> IO(Arrs()):
  (f, r) = fr
  IO.bind(Unit, Arrs(), File.close(f), u => IO.pass(Arrs(), r))

def load.eff(blobs: Bool, f: File, n: U32, k: U32) ->
  IO(File & Result<&1, &1, U32 & String, Arrs()>):
  match blobs:
    case True{}:
      Raw.read_blob_arrays(f, n)
    case False{}:
      Raw.read_arrays(f, n, k)

def load(+blobs: Bool, path: String, n: U32, +k: U32) -> IO(Arrs()):
  IO.bind(File, Arrs(), IO.try(File, File.open(path, "r")),
    f => IO.bind(File & Result<&1, &1, U32 & String, Arrs()>, Arrs(),
      load.eff(blobs, f, n, k), ra.fin))

def nt_of(s: F.PS) -> U32:
  match s:
    case F.PS{w, head, prev, tok, freq, t, n, pos, nt, more}:
      nt

def lsum(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{x, r}:
      lsum(r, (acc + x : U32))

def lens_of(s: F.PS) -> U32:
  match s:
    case F.PS{w, head, prev, tok, freq, t, n, pos, nt, more}:
      lsum(F.lengths(F.to_list(freq, 320)), 0)

def snd(pr: Array<U32> & U32) -> U32:
  (a, v) = pr
  v

def st0(pr: Array<U32> & U32) -> U32:
  (w, n) = pr
  n

def st1(pr: Array<U32> & U32) -> U32:
  (w, +n) = pr
  nt_of(F.parse_arr(F.win(w, n), n))

def st2(pr: Array<U32> & U32) -> U32:
  (w, +n) = pr
  lens_of(F.parse_arr(F.win(w, n), n))

def stage(p: Nat, w: Array<U32>) -> U32:
  match p:
    case 0n:
      st0(F.arr_len(w))
    case 1n+a:
      match a:
        case 0n:
          st1(F.arr_len(w))
        case 1n+b:
          match b:
            case 0n:
              st2(F.arr_len(w))
            case 1n+c:
              match c:
                case 0n:
                  snd(F.arr_len(F.compress_arr(w)))
                case 1n+e:
                  snd(F.arr_len(F.decompress_arr(w)))

def all(+p: Nat, xs: Arrs(), +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{w, r}:
      all(p, r, (acc + stage(p, w) : U32))

def num(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def run(+p: Nat, path: String, n: U32) -> IO(Unit):
  IO.bind(Arrs(), Unit, load(Nat.is_eq(p, 4n), path, n, 1024),
    xs => IO.print(U32.show(all(p, xs, 0))))

def main() -> IO(Unit):
  do IO<Unit>:
    p : String <- IO.try(String, IO.get_env("P"))
    path : String <- IO.try(String, IO.get_env("BZ_IN"))
    size : String <- IO.try(String, IO.get_env("BZ_SIZE"))
    run(num(p), path, U32.from_nat(num(size)))
