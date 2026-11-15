import ContextCorpus.BoundaryRules
import ContextCorpus.UnderAssumptions
import Lean.Util.CollectAxioms

open Lean Elab Command Term Meta

namespace ContextCorpus
set_option maxHeartbeats 0
set_option maxRecDepth 20000

run_cmd do
  for name in #[``forall_valid_encode_iff, ``decode_encode, ``encode_decoded,
      ``encode_viewOf, ``transport, ``rawArgs_of_shape] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => #[``propext, ``Quot.sound, ``Classical.choice].contains n) do
      throwError "unexpected axiom: {name}, {axioms}"
  logInfo "context-boundary proofs: no new axioms"

run_cmd do
  runTermElabM fun _ => do
    let e ← elabTermAndSynthesize (← `(fun (d : PlutusCore.Data.Data)
      (_h : WellShaped d) => rawArgs d)) none
    let (out, _) ← (Blaster.Optimize.Optimize.main e).run default
    let under ← optimizeUnderAssumptions e
    let dataCtor := ``PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
    if out.getUsedConstants.contains dataCtor then
      throwError "ordinary preparation unexpectedly used the conditional encoding rule"
    unless under.getUsedConstants.contains dataCtor do
      throwError "preparation under assumptions failed to use the encoding rule"
    unless under.isLambda && under.bindingBody!.isLambda do
      throwError "preparation dropped a quantified parameter"
    logInfo "conditional encoding rule: ordinary lambda did not fire; explicit hypotheses fired"

end ContextCorpus
