import PlutusCore.UPLC.Optimize.Plan

namespace PlutusCore.UPLC.Optimize.Callback
open PlutusCore.Default PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue

-- Candidate evaluation is a compiler implementation, not a trusted rewrite.
-- Every emitted callback must separately supply a kernel-checked CEK certificate.
/-- A bounded compiler for a *single callback*, not a bound on a context list.
    Return none when compilation has not reached a callback boundary; callers
    must refuse that rewrite or retain an interpreter fallback. -/
def evaluate (sem : BuiltinSemanticsVariant) : Nat → State → Option (Plan CekValue)
  | 0, _ => none
  | _ + 1, .Return [] v => some (.done 0 v)
  | n + 1, s@(.Eval ..) | n + 1, s@(.Return (_ :: _) _) =>
    match step sem s with
    | .Error => some (.error 0)
    | next => (evaluate sem n next).map (Plan.shift 1)
  | _ + 1, _ => none

def integerPlan : Plan CekValue → Option (Plan Int)
  | .done cost (.VCon (.Integer n)) => some (.done cost n)
  | .error cost => some (.error cost)
  | _ => none

def evaluateInteger (sem : BuiltinSemanticsVariant) (limit : Nat) (s : State) : Option (Plan Int) :=
  (evaluate sem limit s).bind integerPlan

theorem evaluateInteger_eq (sem : BuiltinSemanticsVariant) (limit : Nat)
    (s : State) (plan : Plan Int) (h : evaluateInteger sem limit s = some plan) :
    evaluate sem limit s = some (plan.map (fun n => .VCon (.Integer n))) := by
  unfold evaluateInteger at h
  cases he : evaluate sem limit s with
  | none => simp [he] at h
  | some p =>
    cases p with
    | error n => simp [he, integerPlan] at h; subst plan; rfl
    | done n v =>
      cases v with
      | VCon c => cases c <;> simp [he, integerPlan] at h
                  subst plan; rfl
      | _ => simp [he, integerPlan] at h


end PlutusCore.UPLC.Optimize.Callback
