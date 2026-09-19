import Base
import ../src/inflate.bend as I
import ../src/raw.bend as Raw

# Inflate a zlib file: BZ_IN (zlib stream), BZ_SIZE (its size),
# RAW_SIZE (the decompressed size), BZ_OUT (where to write the result).

def Arrs() -> Type:
  List<&1, Array<U32>>

def ra.fin(fr: File & Result<&1, &1, U32 & String, Arrs()>) -> IO(Arrs()):
  (f, r) = fr
  IO.bind(Unit, Arrs(), File.close(f), u => IO.pass(Arrs(), r))

def load(path: String, n: U32) -> IO(Arrs()):
  IO.bind(File, Arrs(), IO.try(File, File.open(path, "r")),
    f => IO.bind(File & Result<&1, &1, U32 & String, Arrs()>, Arrs(),
      Raw.read_arrays(f, n, 1), ra.fin))

def wr.fin(fr: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, r) = fr
  IO.bind(Unit, Unit, IO.pass(Unit, r), u => File.close(f))

def save(path: String, xs: Arrs()) -> IO(Unit):
  IO.bind(File, Unit, IO.try(File, File.open(path, "w")),
    f => IO.bind(File & Result<&1, &1, U32 & String, Unit>, Unit,
      Raw.write_arrays(f, xs), wr.fin))

def run(xs: Arrs(), +olen: U32) -> Arrs():
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, r}:
      [I.inflate(a, 16, olen)]

def num(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def go(path: String, dest: String, +n: Nat, +olen: Nat) -> IO(Unit):
  IO.bind(Arrs(), Unit, load(path, U32.from_nat(n)),
    xs => save(dest, run(xs, U32.from_nat(olen))))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("BZ_IN"))
    dest : String <- IO.try(String, IO.get_env("BZ_OUT"))
    size : String <- IO.try(String, IO.get_env("BZ_SIZE"))
    raw : String <- IO.try(String, IO.get_env("RAW_SIZE"))
    go(path, dest, num(size), num(raw))
