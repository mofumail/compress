import Base

# A byte as eight bits, most significant first.
# Keeping the spec's byte structural (not arithmetic) is what lets every
# law below close by computation instead of word-level reasoning.
type Byte is Data:
  Byte{b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool}

# A stream of bits, and a stream of bytes.
def Bits() -> Data:
  List<&2, Bool>

def Bytes() -> Data:
  List<&2, Byte>

# Raw octets as the host hands them over: one U32 per byte, 0..255.
def Octets() -> Data:
  List<&2, U32>

def val(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def to_u32(x: Byte) -> U32:
  match x:
    case Byte{b0, b1, b2, b3, b4, b5, b6, b7}:
      (val(b0) * 128 + val(b1) * 64 + val(b2) * 32 + val(b3) * 16 +
       val(b4) * 8 + val(b5) * 4 + val(b6) * 2 + val(b7) : U32)

def bit(w: U32, i: Nat) -> Bool:
  U32.is_eq(U32.and(U32.shrn(w, i), 1), 1)

def from_u32(+w: U32) -> Byte:
  Byte{bit(w, 7n), bit(w, 6n), bit(w, 5n), bit(w, 4n),
       bit(w, 3n), bit(w, 2n), bit(w, 1n), bit(w, 0n)}

def encode(xs: Bytes()) -> Octets():
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{to_u32(h), encode(t)}

def decode(ws: Octets()) -> Bytes():
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      Con{from_u32(w), decode(t)}

# A 9-bit symbol. 0..255 are literal bytes, 256 ends a block, 257.. are
# the length and distance codes. Keeping it structural (a bit plus a
# byte) is what makes the header's roundtrip a computation, not a proof
# about machine words.
type Sym is Data:
  Sym{hi: Bool, lo: Byte}

def eq_bool(a: Bool, b: Bool) -> Bool:
  match a b:
    case False{} False{}:
      True{}
    case False{} True{}:
      False{}
    case True{} False{}:
      False{}
    case True{} True{}:
      True{}

def eq_byte(x: Byte, y: Byte) -> Bool:
  match x:
    case Byte{a0, a1, a2, a3, a4, a5, a6, a7}:
      match y:
        case Byte{c0, c1, c2, c3, c4, c5, c6, c7}:
          Bool.and(eq_bool(a0, c0),
          Bool.and(eq_bool(a1, c1),
          Bool.and(eq_bool(a2, c2),
          Bool.and(eq_bool(a3, c3),
          Bool.and(eq_bool(a4, c4),
          Bool.and(eq_bool(a5, c5),
          Bool.and(eq_bool(a6, c6),
                   eq_bool(a7, c7))))))))

def eq_sym(x: Sym, y: Sym) -> Bool:
  match x:
    case Sym{h1, l1}:
      match y:
        case Sym{h2, l2}:
          Bool.and(eq_bool(h1, h2), eq_byte(l1, l2))

# The nine bits of a symbol, most significant first.
def sym_bits(s: Sym) -> Bits():
  match s:
    case Sym{h, l}:
      match l:
        case Byte{b0, b1, b2, b3, b4, b5, b6, b7}:
          [h, b0, b1, b2, b3, b4, b5, b6, b7]

# Index conversions. These sit only in the fast paths, never in a law.
def sym_to_u32(s: Sym) -> U32:
  match s:
    case Sym{h, l}:
      (val(h) * 256 + to_u32(l) : U32)

def sym_from_u32(+w: U32) -> Sym:
  Sym{bit(w, 8n), from_u32(U32.and(w, 255))}

def sym_to_nat(s: Sym) -> Nat:
  U32.to_nat(sym_to_u32(s))

def sym_from_nat(n: Nat) -> Sym:
  sym_from_u32(U32.from_nat(n))
