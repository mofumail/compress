import Base
import ../src/byte.bend as B
import ../src/lz.bend as LZ

def show_octets(ws: List<&2, U32>) -> String:
  List.show(~&2, ~U32, ~U32.show, ws)

def ntok(ts: List<&2, LZ.Tok>) -> Nat:
  List.length(&2, LZ.Tok, ts)

def trip(+ws: List<&2, U32>) -> String:
  +w = B.decode(ws)
  +ts = LZ.parse_all(w)
  "in=" ++ show_octets(B.encode(w)) ++
  " toks=" ++ Nat.show(ntok(ts)) ++
  " out=" ++ show_octets(B.encode(LZ.expand_all(ts)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(trip([1, 2, 3, 1, 2, 3, 1, 2, 3, 4]))
    IO.print(trip([7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]))
    IO.print(trip([65, 66, 67, 68, 65, 66, 67, 68, 65, 66, 67, 68, 65, 66, 67, 99]))
    IO.print(trip([]))
    IO.print(trip([5]))
