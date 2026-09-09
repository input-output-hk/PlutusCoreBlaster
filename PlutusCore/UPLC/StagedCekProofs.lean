import PlutusCore.UPLC.StagedCek

namespace PlutusCore.UPLC.StagedCek
open PlutusCore.Default CekMachine CekValue Term Builtins
open BuiltinFunctions.Evaluate
set_option maxHeartbeats 0

private theorem lookupValue_eq (env : Environment) (index : Nat) :
    lookupValue env index = List.get?Internal env index := by
  induction env generalizing index with
  | nil => cases index <;> rfl
  | cons v rest ih =>
      cases index with
      | zero => rfl
      | succ i => simpa only [lookupValue, List.get?Internal] using ih i


theorem eval_ret_correct (sv : BuiltinSemanticsVariant) (fuel : Nat) :
    (∀ s env t, eval sv fuel s env t = runSteps sv (.Eval s env t) fuel) ∧
    (∀ s v, ret sv fuel s v = runSteps sv (.Return s v) fuel) := by
  induction fuel with
  | zero =>
      constructor <;> intros <;> simp [eval, ret, runSteps]
  | succ n ih =>
      constructor
      · intro s env t
        cases t <;> try simp only [eval]
        all_goals try simp only [ih.1, ih.2]
        case Var x =>
          simp only [lookupValue_eq, runSteps, step]
          split <;> simp_all [runSteps]
        case Constr i ts => cases ts <;> simp only [eval, ih.1, ih.2, runSteps, step]
        all_goals first | rfl | simp [runSteps, step]
      · intro s v
        cases s with
        | nil => simp [ret, runSteps, step]
        | cons frame rest =>
          cases frame with
          | LeftApplicationToTerm body env =>
              simp only [ret, ih.1]
              rfl
          | RightApplicationOfValue f =>
              cases f <;> try simp only [ret, ih.1]
              case VBuiltin b vs expected =>
                cases expected with
                | More arg tail => cases arg <;> simp [ret, ih.2, runSteps, step]
                | One arg =>
                    cases arg <;> simp only [ret, ih.2, runSteps, step, evalBuiltin]
                    case ArgV => split <;> simp_all [runSteps]
              all_goals first | rfl | simp [runSteps, step]
          | LeftApplicationToValue arg =>
              cases v <;> try simp only [ret, ih.1]
              case VBuiltin b vs expected =>
                cases expected with
                | More next tail => cases next <;> simp [ret, ih.2, runSteps, step]
                | One next =>
                    cases next <;> simp only [ret, ih.2, runSteps, step, evalBuiltin]
                    case ArgV => split <;> simp_all [runSteps]
              all_goals first | rfl | simp [runSteps, step]
          | ForceFrame =>
              cases v <;> try simp only [ret, ih.1]
              case VBuiltin b vs expected =>
                cases expected with
                | More next tail => cases next <;> simp [ret, ih.2, runSteps, step]
                | One next =>
                    cases next <;> simp only [ret, ih.2, runSteps, step, evalBuiltin]
                    case ArgQ => split <;> simp_all [runSteps]
              all_goals first | rfl | simp [runSteps, step]
          | ConstructorArgument i vs ts env =>
              cases ts <;> simp [ret, ih.1, ih.2, runSteps, step]
          | CaseScrutinee ts env =>
              rw [ret.eq_def]
              simp only [ih.1, runSteps, step]
              split <;> simp_all [runSteps] <;>
                repeat (first | assumption | rfl | (split <;> simp_all [runSteps]))
              all_goals by_cases h : ts.length = 1 ∨ ts.length = 2 <;>
                simp_all [runSteps] <;> split <;> simp_all [runSteps]

/-- Kernel-checked equality for every machine state, fuel, and builtin semantics
variant, including constructor fields and primitive case branches. -/
theorem run_eq_runSteps (sv : BuiltinSemanticsVariant) (s : State) (fuel : Nat) :
    run sv s fuel = runSteps sv s fuel := by
  cases s with
  | Eval stack env t => exact (eval_ret_correct sv fuel).1 stack env t
  | Return stack v => exact (eval_ret_correct sv fuel).2 stack v
  | Halt v => simp [run, runSteps]
  | Error => simp [run, runSteps]

theorem execute_eq (p : Program) (params : List Term) (fuel : Nat) :
    execute p params fuel = cekExecuteProgram p params fuel := by
  cases p
  simp only [execute, cekExecuteProgram, cekExecuteProgramWithSemanticVariant, run_eq_runSteps]

#print axioms run_eq_runSteps
#print axioms execute_eq
end PlutusCore.UPLC.StagedCek
