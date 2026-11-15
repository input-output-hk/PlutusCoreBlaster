import ContextCorpus.Boundary
import ContextCorpus.Fixtures
import PlutusCore.UPLC.CekMachine
import Lean.Util.CollectAxioms

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
namespace ContextCorpus
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- Direct proof about the original CEK executable, independent of #prep_uplc
    and SMT. Every transaction field, redeemer and spending payload is free.
    It is a spending-purpose calibration, not a full validity contract. -/
theorem fee_execution (v : View) (ownId : PlutusCore.ByteString.ByteString)
    (ownIndex : Int) (datum : Option PlutusCore.Data.Data) :
    cekExecuteProgram corpusFeeProgram.script (spendArgs v ownId ownIndex datum) 1000 =
      if PlutusCore.Integer.lessThanEqualsInteger v.fee 2000000 then
        .Halt (.VCon .Unit) else .Error := by
  cases datum <;> cases h : PlutusCore.Integer.lessThanEqualsInteger v.fee 2000000 <;>
    simp [corpusFeeProgram, spendArgs, viewArgs, rawArgs, encode, cekExecuteProgram,
      cekExecuteProgramWithSemanticVariant, initialState, applyParams, runSteps, step,
      step.folding, evalBuiltin, PlutusCore.UPLC.Builtins.expectedArgs,
      List.get?Internal, PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
      PlutusCore.UPLC.BuiltinFunctions.Data.unConstrData,
      PlutusCore.UPLC.BuiltinFunctions.Data.unIData,
      PlutusCore.UPLC.BuiltinFunctions.List.headList,
      PlutusCore.UPLC.BuiltinFunctions.List.tailList,
      PlutusCore.UPLC.BuiltinFunctions.Pair.fstPair,
      PlutusCore.UPLC.BuiltinFunctions.Pair.sndPair,
      PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
      PlutusCore.UPLC.BuiltinFunctions.Integer.equalsInteger,
      PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanEqualsInteger,
      PlutusCore.Bool.ifThenElse, PlutusCore.Integer.equalsInteger,
      PlutusCore.Pair.fstPair, PlutusCore.Pair.sndPair, h]

theorem fee_accepts_iff (v : View) (ownId : PlutusCore.ByteString.ByteString)
    (ownIndex : Int) (datum : Option PlutusCore.Data.Data) :
    (cekExecuteProgram corpusFeeProgram.script (spendArgs v ownId ownIndex datum) 1000 =
      .Halt (.VCon .Unit)) ↔ v.fee ≤ 2000000 := by
  by_cases h : v.fee ≤ 2000000 <;>
    simp [fee_execution, PlutusCore.Integer.lessThanEqualsInteger, h]

run_cmd do
  for name in #[``fee_execution, ``fee_accepts_iff] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => #[``propext, ``Quot.sound, ``Classical.choice].contains n) do
      throwError "unexpected axiom: {name}, {axioms}"
  Lean.logInfo "original fee executable: kernel-checked, no new axioms"

end ContextCorpus
