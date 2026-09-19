import Base
import ../src/png.bend as P
import ../src/fast.bend as F
import ../src/raw.bend as Raw

# Decode a PNG (BZ_IN, BZ_SIZE bytes) and write its pixels to BZ_OUT as
# a PAM file.

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

def pam(im: P.IM) -> Arrs():
  match im:
    case P.IM{px, +w, +h, +ch, +bps, ok, pal, pch}:
      [F.of_list(P.pam_header(w, h, ch, bps)), px]

def run(xs: Arrs(), +n: U32) -> Arrs():
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, r}:
      pam(P.to_rgb(P.decode(a, n)))

def num(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def go(path: String, dest: String, +n: Nat) -> IO(Unit):
  IO.bind(Arrs(), Unit, load(path, U32.from_nat(n)),
    xs => save(dest, run(xs, U32.from_nat(n))))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("BZ_IN"))
    dest : String <- IO.try(String, IO.get_env("BZ_OUT"))
    size : String <- IO.try(String, IO.get_env("BZ_SIZE"))
    go(path, dest, num(size))
