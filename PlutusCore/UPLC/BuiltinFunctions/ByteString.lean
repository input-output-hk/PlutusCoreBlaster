import PlutusCore.ByteString
import PlutusCore.Default
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.CekValue
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

-- Define appendByteString
def appendByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString x), CekValue.VCon (Const.ByteString y)] =>
      some (CekValue.VCon (Const.ByteString (PLC.appendByteString x y)))
  | _ => none

-- Define consByteString
def consByteString (semanticsVersion : PLC.BuiltinSemanticsVariant) (Vs : List CekValue) : Option CekValue :=
  match semanticsVersion, Vs with
  | .defaultFunSemanticsVariantC, [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.ByteString bs)] => tryCatchSome (PLC.consByteStringV2 x bs) (CekValue.VCon ∘ Const.ByteString)
  | _,                            [CekValue.VCon (Const.Integer x), CekValue.VCon (Const.ByteString bs)] => PLC.consByteStringV1 x bs             |> (CekValue.VCon ∘ Const.ByteString)
  | _, _                                                                                                 => none

-- Define sliceByteString
def sliceByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer s), CekValue.VCon (Const.Integer k), CekValue.VCon (Const.ByteString bs)] =>
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
  | [CekValue.VCon (Const.ByteString bs), CekValue.VCon (Const.Integer j)] =>
      tryCatchSome (PLC.indexByteString bs j) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define equalsByteString
def equalsByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString x), CekValue.VCon (Const.ByteString y)] =>
      some (CekValue.VCon (Const.Bool (PLC.equalsByteString x y)))
  | _ => none

-- Define lessThanByteString
def lessThanByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString x), CekValue.VCon (Const.ByteString y)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanByteString x y)))
  | _ => none

-- Define lessThanEqualsByteString
def lessThanEqualsByteString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString x), CekValue.VCon (Const.ByteString y)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanEqualsByteString x y)))
  | _ => none

end PlutusCore.UPLC.CekValue
