import PlutusCore.UPLC.Optimize.RunSteps

namespace PlutusCore.UPLC.Optimize.Administrative
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- Enter a statically known lambda without inspecting its captured
    environment or evaluating the argument prematurely. -/
theorem apply_lambda (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (body argument : Term) (fuel : Nat) :
    runSteps sem (.Eval k env (.Apply (.Lam body) argument)) fuel =
      if fuel < 3 then .BudgetExhausted else
        runSteps sem (.Eval (.RightApplicationOfValue (.VLam body env) :: k)
          env argument) (fuel - 3) := by
  have block : runStepsPreservingState sem
      (.Eval k env (.Apply (.Lam body) argument)) 3 =
      .Eval (.RightApplicationOfValue (.VLam body env) :: k) env argument := rfl
  have hl : Live (runStepsPreservingState sem
      (.Eval k env (.Apply (.Lam body) argument)) 3) := by rw [block]; trivial
  simpa [block] using runSteps_of_live_prefix sem _ 3 hl fuel

theorem force_delay (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (body : Term) (fuel : Nat) :
    runSteps sem (.Eval k env (.Force (.Delay body))) fuel =
      if fuel < 3 then .BudgetExhausted else
        runSteps sem (.Eval k env body) (fuel - 3) := by
  have block : runStepsPreservingState sem (.Eval k env (.Force (.Delay body))) 3 =
      .Eval k env body := rfl
  have hl : Live (runStepsPreservingState sem (.Eval k env (.Force (.Delay body))) 3) := by
    rw [block]; trivial
  simpa [block] using runSteps_of_live_prefix sem _ 3 hl fuel

theorem return_lambda (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (body : Term) (v : CekValue) (fuel : Nat) :
    runSteps sem (.Return (.RightApplicationOfValue (.VLam body env) :: k) v) fuel =
      if fuel = 0 then .BudgetExhausted else
        runSteps sem (.Eval k (v :: env) body) (fuel - 1) := by
  cases fuel <;> rfl

theorem return_lambda_left (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (body : Term) (v : CekValue) (fuel : Nat) :
    runSteps sem (.Return (.LeftApplicationToValue v :: k) (.VLam body env)) fuel =
      if fuel = 0 then .BudgetExhausted else
        runSteps sem (.Eval k (v :: env) body) (fuel - 1) := by
  cases fuel <;> rfl

/-- Discard an irrelevant environment cell while looking up a later index.
    This is a representation rewrite and consumes no CEK fuel. -/
theorem lookup_tail (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (unused : CekValue) (index fuel : Nat) :
    runSteps sem (.Eval k (unused :: env) (.Var (index + 1))) fuel =
      runSteps sem (.Eval k env (.Var index)) fuel := by
  cases fuel <;> rfl

theorem lookup_head (sem : BuiltinSemanticsVariant) (k : Stack)
    (env : Environment) (v : CekValue) (fuel : Nat) :
    runSteps sem (.Eval k (v :: env) (.Var 0)) fuel =
      if fuel = 0 then .BudgetExhausted else
        runSteps sem (.Return k v) (fuel - 1) := by
  cases fuel <;> rfl

theorem return_empty (sem : BuiltinSemanticsVariant) (v : CekValue) (fuel : Nat) :
    runSteps sem (.Return [] v) fuel =
      if fuel = 0 then .BudgetExhausted else .Halt v := by
  cases fuel with
  | zero => rfl
  | succ n => cases n <;> rfl

end PlutusCore.UPLC.Optimize.Administrative
