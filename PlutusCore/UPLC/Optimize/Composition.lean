import PlutusCore.UPLC.Optimize.Plan
import PlutusCore.UPLC.Optimize.Administrative

namespace PlutusCore.UPLC.Optimize.Composition
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations

def finish (p : Plan CekValue) (fuel : Nat) : State :=
  match p with
  | .done cost v => if fuel ≤ cost then .BudgetExhausted else .Halt v
  | .error before => if fuel ≤ before then .BudgetExhausted else .Error

theorem execute_empty (sem : BuiltinSemanticsVariant) (p : Plan CekValue) (fuel : Nat) :
    Plan.execute sem [] p fuel = finish p fuel := by
  cases p with
  | error before => rfl
  | done cost v =>
    simp only [Plan.execute, finish]
    by_cases hc : fuel < cost
    · simp [hc, show fuel ≤ cost by omega]
    · rw [if_neg hc, Administrative.return_empty]
      have bound : fuel - cost = 0 ↔ fuel ≤ cost := by omega
      simp only [bound]

/-- Compose through identity-returning lambdas without inspecting unused
    captures or materializing a returned CEK state for each list element. -/
theorem execute_identity (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (p : Plan CekValue) (fuel : Nat) :
    Plan.execute sem (.RightApplicationOfValue (.VLam (.Var 0) env) :: k) p fuel =
      Plan.execute sem k (p.bind (fun v => .done 2 v)) fuel := by
  apply Plan.execute_bind
  intro v n
  apply Plan.run_eq
  rfl

/-- A continuation that discards its argument is also independent of the
    producing validator. Failure in the producer still skips the continuation. -/
theorem execute_constant (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (c : Const) (p : Plan CekValue) (fuel : Nat) :
    Plan.execute sem (.RightApplicationOfValue (.VLam (.Const c) env) :: k) p fuel =
      Plan.execute sem k (p.bind (fun _ => .done 2 (.VCon c))) fuel := by
  apply Plan.execute_bind
  intro v n
  apply Plan.run_eq
  rfl

def assertPlan (success : Const) : CekValue → Plan CekValue
  | .VCon (.Bool true) => .done 9 (.VCon success)
  | .VCon (.Bool false) => .error 8
  | _ => .error 6

/-- A generic Boolean assertion consumer, independent of how its Boolean was
    computed. Incorrect result types and the false branch retain their costs. -/
theorem execute_assert (sem : BuiltinSemanticsVariant) (k : Stack)
    (yesEnv noEnv : Environment) (success : Const) (p : Plan CekValue) (fuel : Nat) :
    Plan.execute sem
      (.RightApplicationOfValue (.VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV])) ::
        .LeftApplicationToTerm (.Delay (.Const success)) yesEnv ::
        .LeftApplicationToTerm (.Delay .Error) noEnv :: .ForceFrame :: k) p fuel =
      Plan.execute sem k (p.bind (assertPlan success)) fuel := by
  apply Plan.execute_bind
  intro v n
  apply Plan.run_eq
  cases v with
  | VCon c =>
    cases c <;> first
      | exact ⟨by trivial, by rfl⟩
      | rename_i b; cases b <;> first | rfl | exact ⟨by trivial, by rfl⟩
  | _ => exact ⟨by trivial, by rfl⟩

def conditionalTailPlan (success : Const) : CekValue → Plan CekValue
  | .VCon (.Bool true) => .done 3 (.VCon success)
  | .VCon (.Bool false) => .error 3
  | _ => .error 0

/-- The last application of an if-then-else is shared by constructor/case and
    ordinary application encodings. An error application never evaluates its
    argument, which may contain arbitrary code. -/
theorem conditional_tail (sem : BuiltinSemanticsVariant) (k : Stack)
    (yesEnv noEnv : Environment) (success : Const) (errorArgument : Term)
    (v : CekValue) (fuel : Nat) :
    runSteps sem
      (.Return (.LeftApplicationToValue (.VDelay (.Apply .Error errorArgument) noEnv) ::
          .ForceFrame :: k)
        (.VBuiltin .IfThenElse [.VDelay (.Const success) yesEnv, v] a[ArgV])) fuel =
      Plan.execute sem k (conditionalTailPlan success v) fuel := by
  apply Plan.run_eq
  cases v with
  | VCon c =>
    cases c <;> first
      | exact ⟨by trivial, by rfl⟩
      | rename_i b; cases b <;> first | rfl | exact ⟨by trivial, by rfl⟩
  | _ => exact ⟨by trivial, by rfl⟩

end PlutusCore.UPLC.Optimize.Composition
