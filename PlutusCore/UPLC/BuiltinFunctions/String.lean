import PlutusCore.String
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.BuiltinFunctions.String

namespace PLC
  open PlutusCore.String
  export PlutusCore.String (
    appendString
    equalsString
    encodeUtf8
    decodeUtf8
  )
end PLC

open PlutusCore.UPLC.BuiltinFunctions.Utils
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define appendString
def appendString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.String op2), CekValue.VCon (Const.String op1)] =>
      some (CekValue.VCon (Const.String (PLC.appendString op1 op2)))
  | _ => none

-- Define equalsString
def equalsString (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.String op2), CekValue.VCon (Const.String op1)] =>
      some (CekValue.VCon (Const.Bool (PLC.equalsString op1 op2)))
  | _ => none


-- Define encodeUtf8
def encodeUtf8 (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.String s)] =>
      some (CekValue.VCon (Const.ByteString (PLC.encodeUtf8 s)))
  | _ => none

-- Define decodeUtf8
def decodeUtf8 (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ByteString bs)] =>
      tryCatchSome (PLC.decodeUtf8 bs) (CekValue.VCon ∘ Const.String)
  | _ => none


end PlutusCore.UPLC.BuiltinFunctions.String
