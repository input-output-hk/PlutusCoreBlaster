import PlutusCore.ByteString
import PlutusCore.Default
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.BuiltinFunctions.ByteString

namespace PLC
  open PlutusCore.ByteString
  export PlutusCore.ByteString (
    appendByteString
    consByteStringV1
    consByteStringV2
    sliceByteString
    lengthOfByteString
    indexByteString
    equalsByteString
    lessThanByteString
    lessThanEqualsByteString
  )
  open PlutusCore.Default
  export PlutusCore.Default (
    BuiltinSemanticsVariant
  )
end PLC

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.BuiltinFunctions.Utils

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define appendByteString
def appendByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString op2), CekValue.VCon (Const.ByteString op1)] =>
      some (CekValue.VCon (Const.ByteString (PLC.appendByteString op1 op2)))
  | _ => none

-- Define consByteString
def consByteString (semanticsVersion : PLC.BuiltinSemanticsVariant) (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString bs), CekValue.VCon (Const.Integer x)] =>
       match semanticsVersion with
       | .defaultFunSemanticsVariantC => tryCatchSome (PLC.consByteStringV2 x bs) (CekValue.VCon ∘ Const.ByteString)
       | _ => some (CekValue.VCon (Const.ByteString (PLC.consByteStringV1 x bs)))
  | _ => none

-- Define sliceByteString
def sliceByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString bs), CekValue.VCon (Const.Integer k), CekValue.VCon (Const.Integer s)] =>
      some (CekValue.VCon (Const.ByteString (PLC.sliceByteString s k bs)))
  | _ => none

-- Define lengthOfByteString
def lengthOfByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString bs)] =>
      some (CekValue.VCon (Const.Integer (PLC.lengthOfByteString bs)))
  | _ => none

-- Define indexByteString
def indexByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer j), CekValue.VCon (Const.ByteString bs)] =>
      tryCatchSome (PLC.indexByteString bs j) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define equalsByteString
def equalsByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString op2), CekValue.VCon (Const.ByteString op1)] =>
      some (CekValue.VCon (Const.Bool (PLC.equalsByteString op1 op2)))
  | _ => none

-- Define lessThanByteString
def lessThanByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString op2), CekValue.VCon (Const.ByteString op1)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanByteString op1 op2)))
  | _ => none

-- Define lessThanEqualsByteString
def lessThanEqualsByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString op2), CekValue.VCon (Const.ByteString op1)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanEqualsByteString op1 op2)))
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.ByteString
