import ContextCorpus.Boundary
import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.PlutusScript
import Lean.Data.Json

namespace ContextCorpus
open Lean
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.PlutusScript

/-- Concrete diagnostic replay only. These counts do not bound symbolic lists
    and are not proofs of a universally quantified script property. -/
def replay (script : PlutusScript) (ctx : PlutusCore.Data.Data) (limit : Nat := 100000) : Json := Id.run do
  let .Program _ body := script.script
  let mut state := initialState (applyParams body (rawArgs ctx))
  let mut steps := 0
  let mut maxStack := 0
  let mut maxEnv := 0
  let mut result := "budget_exhausted"
  for _ in [:limit] do
    match state with
    | .Halt (.VCon .Unit) => result := "accept"; break
    | .Halt _ => result := "other"; break
    | .Error => result := "reject"; break
    | .BudgetExhausted => break
    | .Eval k env _ => maxStack := max maxStack k.length; maxEnv := max maxEnv env.length
    | .Return k _ => maxStack := max maxStack k.length
    state := step default state
    steps := steps + 1
  return Json.mkObj [("result", toJson result), ("steps", toJson steps),
    ("max_stack", toJson maxStack), ("max_current_env", toJson maxEnv)]

end ContextCorpus
