import PlutusCore.Bitwise.Basic
import PlutusCore.UPLC.CekValue

namespace PlutusCore.UPLC.BuiltinFunctions.Bitwise

open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.Bitwise

-- NOTE: Args are deliberately reversed on the CEK machine stack (last arg first).

-- integerToByteString e w n  →  stack [n, w, e]
def integerToByteString : List CekValue → Option CekValue
  | [.VCon (.Integer n), .VCon (.Integer w), .VCon (.Bool e)] =>
    match PlutusCore.Bitwise.integerToByteString e w n with
    | .ok s    => .some (.VCon (.ByteString ⟨s⟩))
    | .error _ => .none
  | _ => .none

-- byteStringToInteger e s  →  stack [s, e]
def byteStringToInteger : List CekValue → Option CekValue
  | [.VCon (.ByteString s), .VCon (.Bool e)] =>
    .some (.VCon (.Integer (PlutusCore.Bitwise.byteStringToInteger e s.data)))
  | _ => .none

-- andByteString e b c  →  stack [c, b, e]
def andByteString : List CekValue → Option CekValue
  | [.VCon (.ByteString c), .VCon (.ByteString b), .VCon (.Bool e)] =>
    .some (.VCon (.ByteString ⟨PlutusCore.Bitwise.andByteString e b.data c.data⟩))
  | _ => .none

-- orByteString e b c  →  stack [c, b, e]
def orByteString : List CekValue → Option CekValue
  | [.VCon (.ByteString c), .VCon (.ByteString b), .VCon (.Bool e)] =>
    .some (.VCon (.ByteString ⟨PlutusCore.Bitwise.orByteString e b.data c.data⟩))
  | _ => .none

-- xorByteString e b c  →  stack [c, b, e]
def xorByteString : List CekValue → Option CekValue
  | [.VCon (.ByteString c), .VCon (.ByteString b), .VCon (.Bool e)] =>
    .some (.VCon (.ByteString ⟨PlutusCore.Bitwise.xorByteString e b.data c.data⟩))
  | _ => .none

-- complementByteString b  →  stack [b]
def complementByteString : List CekValue → Option CekValue
  | [.VCon (.ByteString b)] =>
    .some (.VCon (.ByteString ⟨PlutusCore.Bitwise.complementByteString b.data⟩))
  | _ => .none

-- readBit s i  →  stack [i, s]
def readBit : List CekValue → Option CekValue
  | [.VCon (.Integer i), .VCon (.ByteString s)] =>
    match PlutusCore.Bitwise.readBit s.data i with
    | .ok b    => .some (.VCon (.Bool b))
    | .error _ => .none
  | _ => .none

-- writeBits s idxs x  →  stack [x, idxs, s]
def writeBits : List CekValue → Option CekValue
  | [.VCon (.Bool x), .VCon (.ConstList idxs), .VCon (.ByteString s)] =>
    let ixList := idxs.filterMap (fun c => match c with | .Integer i => .some i | _ => .none)
    match PlutusCore.Bitwise.writeBits s.data ixList x with
    | .ok s'   => .some (.VCon (.ByteString ⟨s'⟩))
    | .error _ => .none
  | _ => .none

-- replicateByte n b  →  stack [b, n]
def replicateByte : List CekValue → Option CekValue
  | [.VCon (.Integer b), .VCon (.Integer n)] =>
    match PlutusCore.Bitwise.replicateByte n b with
    | .ok s    => .some (.VCon (.ByteString ⟨s⟩))
    | .error _ => .none
  | _ => .none

-- shiftByteString s k  →  stack [k, s]
def shiftByteString : List CekValue → Option CekValue
  | [.VCon (.Integer k), .VCon (.ByteString s)] =>
    .some (.VCon (.ByteString ⟨PlutusCore.Bitwise.shiftByteString s.data k⟩))
  | _ => .none

-- rotateByteString s k  →  stack [k, s]
def rotateByteString : List CekValue → Option CekValue
  | [.VCon (.Integer k), .VCon (.ByteString s)] =>
    .some (.VCon (.ByteString ⟨PlutusCore.Bitwise.rotateByteString s.data k⟩))
  | _ => .none

-- countSetBits s  →  stack [s]
def countSetBits : List CekValue → Option CekValue
  | [.VCon (.ByteString s)] =>
    .some (.VCon (.Integer (PlutusCore.Bitwise.countSetBits s.data)))
  | _ => .none

-- findFirstSetBit s  →  stack [s]
def findFirstSetBit : List CekValue → Option CekValue
  | [.VCon (.ByteString s)] =>
    .some (.VCon (.Integer (PlutusCore.Bitwise.findFirstSetBit s.data)))
  | _ => .none

end PlutusCore.UPLC.BuiltinFunctions.Bitwise
