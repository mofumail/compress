import Base
import ../src/byte.bend as B
import ../src/lz.bend as LZ
import ../src/fast.bend as F
import ../src/codec.bend as Codec

# The fast codec against the proven reference: its tokens must expand,
# under the reference decoder, back to the input.

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

def tok1(+v: U32, big: Bool) -> LZ.Tok:
  match big:
    case False{}:
      LZ.Lit{B.from_u32(v)}
    case True{}:
      LZ.Ref{U32.to_nat(((v .&. 65535 : U32) + 1 : U32)),
        U32.to_nat(((v >> 16n : U32) .&. 511 : U32))}

def conv(ts: List<&2, U32>) -> List<&2, LZ.Tok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+v, r}:
      Con{tok1(v, U32.is_ne((v .&. 2147483648 : U32), 0)), conv(r)}

def check(+ws: List<&2, U32>) -> String:
  +ts = F.toks(F.parse(ws))
  "tokens=" ++ Nat.show(List.length(&2, U32, ts)) ++ " reference-decodes-to-input: " ++
    Bool.show(same(B.encode(LZ.expand_fast_all(conv(ts))), ws))

# fast encoder -> reference chunk decoder
def check_enc(+ws: List<&2, U32>) -> String:
  +blob = F.compress_chunk(ws)
  "chunk bytes=" ++ Nat.show(List.length(&2, U32, blob)) ++
  " reference-decodes-fast-chunk: " ++
    Bool.show(same(B.encode(Codec.decomp_chunk(B.decode(blob))), ws))

# fast decoder on the fast encoder's chunk, and on the reference's chunk
def check_dec(+ws: List<&2, U32>) -> String:
  "fast->fast: " ++ Bool.show(same(F.decompress_chunk(F.compress_chunk(ws)), ws)) ++
  " reference->fast: " ++ Bool.show(same(F.decompress_chunk(
    B.encode(Codec.comp_chunk(B.decode(ws)))), ws))

def both(+ws: List<&2, U32>) -> String:
  check(ws) ++ "\n" ++ check_enc(ws) ++ "\n" ++ check_dec(ws)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(check([7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]))
    IO.print(check([1, 2, 3, 1, 2, 3, 1, 2, 3, 4]))
    IO.print(check([5]))
    path : String <- IO.try(String, IO.get_env("BZ_IN"))
    size : String <- IO.try(String, IO.get_env("BZ_SIZE"))
    ws : List<&2, U32> <- read_file(path,
      U32.from_nat(Maybe.default(&2, Nat, Nat.read(size), 0n)))
    IO.print(both(ws))
    IO.print(both([7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]))
    IO.print(both([5]))
    IO.print(both([]))
