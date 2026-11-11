import PlutusCore.UPLC
import Blaster

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.CekMachine

def dispatch (branches : List Term) (b : Bool) : State :=
  step .defaultFunSemanticsVariantE
    (.Return [.CaseScrutinee branches []] (.VCon (.Bool b)))

def selected (state : State) (expected : Int) : Prop :=
  match state with
  | .Eval [] [] (.Const (.Integer actual)) => actual = expected
  | _ => False

def failed (state : State) : Prop :=
  match state with
  | .Error => True
  | _ => False

-- Symbolic builtin booleans must reduce before the full CEK datatype reaches SMT.
#blaster [∀ b : Bool, selected (dispatch [.Const (.Integer 7), .Const (.Integer 9)] b) (if b then 9 else 7)]
#blaster [∀ b : Bool, selected (dispatch [.Const (.Integer 7)] b) 7 ↔ b = false]
#blaster [∀ b : Bool, failed (dispatch [.Const (.Integer 7)] b) ↔ b = true]
#blaster [∀ b : Bool, failed (dispatch [] b)]
#blaster [∀ b : Bool, failed (dispatch [.Const .Unit, .Const .Unit, .Const .Unit] b)]
