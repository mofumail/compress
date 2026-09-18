import Base
import ../src/byte.bend as B
import ../src/lz.bend as LZ

# Differential test: the fast ring-buffer decoder must agree with the
# reference decoder (the one LAWS.bend talks about) on real token
# streams, including long files where distances reach the full window.

def rd.fin(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) ->
  IO(List<&2, U32>):
  (f, r) = fr
  IO.bind(Unit, List<&2, U32>, File.close(f), u => IO.pass(List<&2, U32>, r))

def rd.go(n: U32, f: File) -> IO(List<&2, U32>):
  IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>,
    List<&2, U32>, File.read_bytes(f, n), rd.fin)

def read_file(path: String, n: U32) -> IO(List<&2, U32>):
  IO.bind(File, List<&2, U32>, IO.try(File, File.open(path, "r")), rd.go(n))

def same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      List.is_empty(&2, U32, ys)
    case Con{+a, r}:
      match ys:
        case Nil{}:
          False{}
        case Con{+b, s}:
          Bool.and(U32.is_eq(a, b), same(r, s))

def check(+ws: List<&2, U32>) -> String:
  +ts = LZ.parse_all(B.decode(ws))
  +fast = B.encode(LZ.expand_fast_all(ts))
  "tokens=" ++ Nat.show(List.length(&2, LZ.Tok, ts)) ++
  " fast==input: " ++ Bool.show(same(fast, ws)) ++
  " fast==reference: " ++ Bool.show(same(fast, B.encode(LZ.expand_all(ts))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(check([7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]))
    IO.print(check([1, 2, 3, 1, 2, 3, 1, 2, 3, 4]))
    path : String <- IO.try(String, IO.get_env("BZ_IN"))
    size : String <- IO.try(String, IO.get_env("BZ_SIZE"))
    ws : List<&2, U32> <- read_file(path,
      U32.from_nat(Maybe.default(&2, Nat, Nat.read(size), 0n)))
    IO.print(check(ws))
