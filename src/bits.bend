import Base
import ./byte.bend as Byte

# MSB-first packing of a bit stream into whole bytes. A final partial
# group is padded with zero bits; `padding` names exactly that padding,
# which is what makes the roundtrip law below an equality rather than a
# prefix statement.
def pack(bs: Byte.Bits()) -> Byte.Bytes():
  match bs:
    case Nil{}:
      Nil{}
    case Con{b0, r0}:
      match r0:
        case Nil{}:
          Con{Byte.Byte{b0, False{}, False{}, False{}, False{}, False{}, False{}, False{}}, Nil{}}
        case Con{b1, r1}:
          match r1:
            case Nil{}:
              Con{Byte.Byte{b0, b1, False{}, False{}, False{}, False{}, False{}, False{}}, Nil{}}
            case Con{b2, r2}:
              match r2:
                case Nil{}:
                  Con{Byte.Byte{b0, b1, b2, False{}, False{}, False{}, False{}, False{}}, Nil{}}
                case Con{b3, r3}:
                  match r3:
                    case Nil{}:
                      Con{Byte.Byte{b0, b1, b2, b3, False{}, False{}, False{}, False{}}, Nil{}}
                    case Con{b4, r4}:
                      match r4:
                        case Nil{}:
                          Con{Byte.Byte{b0, b1, b2, b3, b4, False{}, False{}, False{}}, Nil{}}
                        case Con{b5, r5}:
                          match r5:
                            case Nil{}:
                              Con{Byte.Byte{b0, b1, b2, b3, b4, b5, False{}, False{}}, Nil{}}
                            case Con{b6, r6}:
                              match r6:
                                case Nil{}:
                                  Con{Byte.Byte{b0, b1, b2, b3, b4, b5, b6, False{}}, Nil{}}
                                case Con{b7, r7}:
                                  Con{Byte.Byte{b0, b1, b2, b3, b4, b5, b6, b7}, pack(r7)}

# The zero bits `pack` appends to close the final byte.
def padding(bs: Byte.Bits()) -> Byte.Bits():
  match bs:
    case Nil{}:
      Nil{}
    case Con{b0, r0}:
      match r0:
        case Nil{}:
          [False{}, False{}, False{}, False{}, False{}, False{}, False{}]
        case Con{b1, r1}:
          match r1:
            case Nil{}:
              [False{}, False{}, False{}, False{}, False{}, False{}]
            case Con{b2, r2}:
              match r2:
                case Nil{}:
                  [False{}, False{}, False{}, False{}, False{}]
                case Con{b3, r3}:
                  match r3:
                    case Nil{}:
                      [False{}, False{}, False{}, False{}]
                    case Con{b4, r4}:
                      match r4:
                        case Nil{}:
                          [False{}, False{}, False{}]
                        case Con{b5, r5}:
                          match r5:
                            case Nil{}:
                              [False{}, False{}]
                            case Con{b6, r6}:
                              match r6:
                                case Nil{}:
                                  [False{}]
                                case Con{b7, r7}:
                                  padding(r7)

def unpack(ys: Byte.Bytes()) -> Byte.Bits():
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      match y:
        case Byte.Byte{b0, b1, b2, b3, b4, b5, b6, b7}:
          Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, unpack(t)}}}}}}}}
