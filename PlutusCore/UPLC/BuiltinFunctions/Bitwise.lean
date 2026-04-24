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
  | [CekValue.VCon (Const.Integer n), CekValue.VCon (Const.Integer w), CekValue.VCon (Const.Bool e)] =>
      tryCatchSome (PLC.integerToByteString e w n) (fun r => CekValue.VCon (Const.ByteString ⟨r⟩))
  | _ => none

-- Define byteStringToInteger: args reversed as [bs, e]
def byteStringToInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString bs), CekValue.VCon (Const.Bool e)] =>
      some (CekValue.VCon (Const.Integer (PLC.byteStringToInteger e bs.data)))
  | _ => none

-- Define andByteString: args reversed as [op2, op1, e]
def andByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString op2), CekValue.VCon (Const.ByteString op1), CekValue.VCon (Const.Bool e)] =>
      some (CekValue.VCon (Const.ByteString ⟨PLC.andByteString e op1.data op2.data⟩))
  | _ => none

-- Define orByteString: args reversed as [op2, op1, e]
def orByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString op2), CekValue.VCon (Const.ByteString op1), CekValue.VCon (Const.Bool e)] =>
      some (CekValue.VCon (Const.ByteString ⟨PLC.orByteString e op1.data op2.data⟩))
  | _ => none

-- Define xorByteString: args reversed as [op2, op1, e]
def xorByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString op2), CekValue.VCon (Const.ByteString op1), CekValue.VCon (Const.Bool e)] =>
      some (CekValue.VCon (Const.ByteString ⟨PLC.xorByteString e op1.data op2.data⟩))
  | _ => none

-- Define complementByteString
def complementByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString bs)] =>
      some (CekValue.VCon (Const.ByteString ⟨PLC.complementByteString bs.data⟩))
  | _ => none

-- Define shiftByteString: args reversed as [k, s]
def shiftByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer k), CekValue.VCon (Const.ByteString s)] =>
      some (CekValue.VCon (Const.ByteString ⟨PLC.shiftByteString s.data k⟩))
  | _ => none

-- Define rotateByteString: args reversed as [k, s]
def rotateByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer k), CekValue.VCon (Const.ByteString s)] =>
      some (CekValue.VCon (Const.ByteString ⟨PLC.rotateByteString s.data k⟩))
  | _ => none

-- Define countSetBits
def countSetBits (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString s)] =>
      some (CekValue.VCon (Const.Integer (PLC.countSetBits s.data)))
  | _ => none

-- Define findFirstSetBit
def findFirstSetBit (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString s)] =>
      some (CekValue.VCon (Const.Integer (PLC.findFirstSetBit s.data)))
  | _ => none

-- Define readBit: args reversed as [i, s]
def readBit (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer i), CekValue.VCon (Const.ByteString s)] =>
      tryCatchSome (PLC.readBit s.data i) (CekValue.VCon ∘ Const.Bool)
  | _ => none

-- Define writeBits: args reversed as [x, ixs, s]
def writeBits (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Bool x), CekValue.VCon (Const.ConstList ixs), CekValue.VCon (Const.ByteString s)] =>
      match ixs.mapM (fun c => match c with | Const.Integer i => some i | _ => none) with
      | some intList => tryCatchSome (PLC.writeBits s.data intList x) (fun r => CekValue.VCon (Const.ByteString ⟨r⟩))
      | none => none
  | _ => none

-- Define replicateByte: args reversed as [b, l]
def replicateByte (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer b), CekValue.VCon (Const.Integer l)] =>
      tryCatchSome (PLC.replicateByte l b) (fun r => CekValue.VCon (Const.ByteString ⟨r⟩))
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.Bitwise
