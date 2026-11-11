import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.Utils

open PlutusCore.Integer (Integer)
open CekMachine
open CekValue (CekValue)
open Term

/-! Helpers and Predicates -/

/-- Return CekValue from in Halt State, if any -/
def fromHaltState (s : State) : Option CekValue :=
  match s with
  | .Halt cv => some cv
  | _ => none

/-- Return Integer from Halt State, if any -/
def fromFrameToInt (s : State): Option Integer :=
  match s with
  | .Halt (.VCon (Const.Integer x)) => some x
  | _ => none

def isErrorState : State -> Prop
 | State.Error => True
 | _ => False

def isHaltState : State -> Prop
 | .Halt _ => True
 | _ => False

/-- An unfinished execution at the verification step limit. This is not rejection. -/
def isExhausted : State → Prop
 | .BudgetExhausted => True
 | _ => False

def isSuccessful := isHaltState

/-- Execution is considered as unsuccessful when evaluation ends with either Error or BudgetExhausted -/
def isUnsuccessful : State → Prop
 | .Error
 | .BudgetExhausted => True
 | _ => False

end PlutusCore.UPLC.Utils
