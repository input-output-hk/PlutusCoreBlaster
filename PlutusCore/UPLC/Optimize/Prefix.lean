import PlutusCore.UPLC.Optimize.RunSteps

namespace PlutusCore.UPLC.Optimize
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine

/-- A finite administrative block, with a definitional execution certificate.
    The live endpoint guarantees that smaller fuel could not have halted or
    failed earlier. -/
structure Prefix (sem : BuiltinSemanticsVariant) where
  entry : State
  target : State
  cost : Nat
  correct : runStepsPreservingState sem entry cost = target
  live : Live target

namespace Prefix

def start (sem : BuiltinSemanticsVariant) (block : Prefix sem) : State := block.entry

theorem run_eq (sem : BuiltinSemanticsVariant) (block : Prefix sem) (fuel : Nat) :
    runSteps sem (start sem block) fuel =
      if fuel < block.cost then .BudgetExhausted else
        runSteps sem block.target (fuel - block.cost) := by
  have hl : Live (runStepsPreservingState sem block.entry block.cost) := by
    rw [block.correct]; exact block.live
  simpa only [start, block.correct] using runSteps_of_live_prefix sem block.entry block.cost hl fuel

end Prefix
end PlutusCore.UPLC.Optimize
