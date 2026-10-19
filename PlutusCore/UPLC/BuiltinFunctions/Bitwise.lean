import PlutusCore.Bitwise
import PlutusCore.ByteString
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.BuiltinFunctions.Bitwise

namespace PLC
  open PlutusCore.Bitwise
  export PlutusCore.Bitwise (
    integerToByteString
    byteStringToInteger
    andByteString
    orByteString
    xorByteString
    complementByteString
    shiftByteString
    rotateByteString
    countSetBits
    findFirstSetBit
    readBit
    writeBits
    replicateByte
  )
end PLC

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.BuiltinFunctions.Utils
open PlutusCore.ByteString

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define integerToByteString: args reversed as [n, w, e]
def integerToByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Integer n), .VCon (.Integer w), .VCon (.Bool e)] =>
      tryCatchSome (PLC.integerToByteString e w n) (fun r => .VCon (.ByteString ⟨r⟩))
  | _ => none

-- Define byteStringToInteger: args reversed as [bs, e]
def byteStringToInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ByteString bs), .VCon (.Bool e)] =>
      some (.VCon (.Integer (PLC.byteStringToInteger e bs.data)))
  | _ => none

-- Define andByteString: args reversed as [op2, op1, e]
def andByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ByteString op2), .VCon (.ByteString op1), .VCon (.Bool e)] =>
      some (.VCon (.ByteString ⟨PLC.andByteString e op1.data op2.data⟩))
  | _ => none

-- Define orByteString: args reversed as [op2, op1, e]
def orByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ByteString op2), .VCon (.ByteString op1), .VCon (.Bool e)] =>
      some (.VCon (.ByteString ⟨PLC.orByteString e op1.data op2.data⟩))
  | _ => none

-- Define xorByteString: args reversed as [op2, op1, e]
def xorByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ByteString op2), .VCon (.ByteString op1), .VCon (.Bool e)] =>
      some (.VCon (.ByteString ⟨PLC.xorByteString e op1.data op2.data⟩))
  | _ => none

-- Define complementByteString
def complementByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ByteString bs)] =>
      some (.VCon (.ByteString ⟨PLC.complementByteString bs.data⟩))
  | _ => none

-- Define shiftByteString: args reversed as [k, s]
def shiftByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Integer k), .VCon (.ByteString s)] =>
      -- Plutus requires the integer arg to fit in Int64; reject out-of-range values.
      if k > 9223372036854775807 || k < -9223372036854775808 then none
      else some (.VCon (.ByteString ⟨PLC.shiftByteString s.data k⟩))
  | _ => none

-- Define rotateByteString: args reversed as [k, s]
def rotateByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Integer k), .VCon (.ByteString s)] =>
      -- Plutus requires the integer arg to fit in Int64; reject out-of-range values.
      if k > 9223372036854775807 || k < -9223372036854775808 then none
      else some (.VCon (.ByteString ⟨PLC.rotateByteString s.data k⟩))
  | _ => none

-- Define countSetBits
def countSetBits (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ByteString s)] =>
      some (.VCon (.Integer (PLC.countSetBits s.data)))
  | _ => none

-- Define findFirstSetBit
def findFirstSetBit (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ByteString s)] =>
      some (.VCon (.Integer (PLC.findFirstSetBit s.data)))
  | _ => none

-- Define readBit: args reversed as [i, s]
def readBit (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Integer i), .VCon (.ByteString s)] =>
      tryCatchSome (PLC.readBit s.data i) (.VCon ∘ .Bool)
  | _ => none

-- Define writeBits: args reversed as [x, ixs, s]
def writeBits (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Bool x), .VCon (.ConstList ixs), .VCon (.ByteString s)] =>
      match ixs.mapM (fun c => match c with | .Integer i => some i | _ => none) with
      | some intList => tryCatchSome (PLC.writeBits s.data intList x) (fun r => .VCon (.ByteString ⟨r⟩))
      | none => none
  | _ => none

-- Define replicateByte: args reversed as [b, l]
def replicateByte (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Integer b), .VCon (.Integer l)] =>
      tryCatchSome (PLC.replicateByte l b) (fun r => .VCon (.ByteString ⟨r⟩))
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.Bitwise
