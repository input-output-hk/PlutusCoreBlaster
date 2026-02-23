import PlutusCore.Integer
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.CekValue
namespace PLC
  open PlutusCore.Integer
  export PlutusCore.Integer (
    addInteger
    subtractInteger
    multiplyInteger
    divideInteger
    modInteger
    quotientInteger
    remainderInteger
    equalsInteger
    lessThanInteger
    lessThanInteger
    lessThanEqualsInteger
  )
end PLC
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define addInteger
def addInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      some (CekValue.VCon (Const.Integer (PLC.addInteger op1 op2)))
  | _ => none

-- Define subtractInteger
def subtractInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      some (CekValue.VCon (Const.Integer (PLC.subtractInteger op1 op2)))
  | _ => none

-- Define multiplyInteger
def multiplyInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      some (CekValue.VCon (Const.Integer (PLC.multiplyInteger op1 op2)))
  | _ => none

-- Define divideInteger (truncates towards negative infinity)
def divideInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
       tryCatchSome (PLC.divideInteger op1 op2) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define modInteger (truncates towards negative infinity)
def modInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      tryCatchSome (PLC.modInteger op1 op2) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define quotientInteger (truncates towards zero)
def quotientInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      tryCatchSome (PLC.quotientInteger op1 op2) (CekValue.VCon ∘ Const.Integer)
  | _ => none

-- Define remainderInteger (truncates towards zero)
def remainderInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      tryCatchSome (PLC.remainderInteger op1 op2) (CekValue.VCon ∘ Const.Integer)
  | _ => none


-- Define equalsInteger
def equalsInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      some (CekValue.VCon (Const.Bool (PLC.equalsInteger op1 op2)))
  | _ => none

-- Define lessThanInteger
def lessThanInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanInteger op1 op2)))
  | _ => none

-- Define lessThanEqualsInteger
def lessThanEqualsInteger (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Integer op2), CekValue.VCon (Const.Integer op1)] =>
      some (CekValue.VCon (Const.Bool (PLC.lessThanEqualsInteger op1 op2)))
  | _ => none

end PlutusCore.UPLC.CekValue
