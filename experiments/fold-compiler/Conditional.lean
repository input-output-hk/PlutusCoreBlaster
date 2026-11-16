import PlutusCore.UPLC.CekMachine
import ContextCorpus.Boundary
import ContextCorpus.UnderAssumptions
import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.ScriptEncoding
import PlutusCore.UPLC.Optimize.FoldExtension
open Lean Elab Command Term Meta ContextCorpus
set_option maxHeartbeats 0
set_option maxRecDepth 20000
#import_uplc script PlutusV3 single_cbor_hex "experiments/fold-compiler/sum-if-asset.hex"

partial def nodes (root : Lean.Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    unless seen.contains e do
      seen := seen.insert e
      match e with
      | .app f a => todo := f :: a :: todo
      | .lam _ t b _ | .forallE _ t b _ => todo := t :: b :: todo
      | .letE _ t v b _ => todo := t :: v :: b :: todo
      | .mdata _ b | .proj _ _ b => todo := b :: todo
      | _ => pure ()
  return seen.size



run_cmd do
  runTermElabM fun _ => do
    let e ← elabTermAndSynthesize (← `(fun (xs : List (PlutusCore.Data.Data × PlutusCore.Data.Data)) (asset : PlutusCore.ByteString.ByteString) => PlutusCore.UPLC.CekMachine.cekExecuteProgram script.script [.Const (.Data (.Map xs)), .Const (.Data (.B asset))] 1000)) none
    let start ← IO.monoMsNow
    let out ← (Blaster.Optimize.Optimize.main e).run' default
    let elapsed := (← IO.monoMsNow) - start
    if out.hasFVar || out.hasMVar then throwError "optimized output is not closed"
    let constants := out.getUsedConstants
    let evaluator := constants.contains `PlutusCore.UPLC.CekMachine.runSteps ||
      constants.contains `PlutusCore.UPLC.CekMachine.step
    let traversal := constants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.traversalPlan")
    let search := constants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.searchPlan")
    let mut body := out.consumeMData
    while body.isLambda do body := body.bindingBody!.consumeMData
    let exhausted := body.isConstOf `PlutusCore.UPLC.CekMachine.State.BudgetExhausted
    let folded := constants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.foldPlan" || n.toString.startsWith "PlutusCore.UPLC.Optimize.CompiledFold.dataSummary")
    unless folded && !evaluator do throwError "conditional callback was not compiled"
    let result := Json.mkObj [("fold", toJson folded), ("nodes", toJson (nodes out)), ("optimization_ms", toJson elapsed),
      ("evaluator", toJson evaluator), ("traversal", toJson traversal),
      ("search", toJson search), ("always_budget_exhausted", toJson exhausted)]
    logInfo m!"CORPUS_RESULT {result.compress}"

-- Exercise the real command, including its environment rollback boundary.
def conditionalArgs (input : List (PlutusCore.Data.Data × PlutusCore.Data.Data) ×
    PlutusCore.ByteString.ByteString) : List PlutusCore.UPLC.Term.Term :=
  [.Const (.Data (.Map input.1)), .Const (.Data (.B input.2))]
#prep_uplc preparedConditional script conditionalArgs 10000
run_cmd do
  let info ← getConstInfo `preparedConditional.prop
  let some value := info.value? | throwError "missing prepared definition"
  let constants := value.getUsedConstants
  if constants.contains `PlutusCore.UPLC.CekMachine.runSteps ||
      constants.contains `PlutusCore.UPLC.CekMachine.step then
    throwError "prepared conditional still contains the CEK interpreter"
  logInfo "prep_uplc conditional emitted successfully"
