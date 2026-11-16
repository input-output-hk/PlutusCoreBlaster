import PlutusCore.UPLC.ScriptEncoding
import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.Optimize.FoldExtension
import ContextCorpus.Boundary
open ContextCorpus
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false
-- Run bench.py once to materialize these exact corpus artifacts.
#import_uplc withdrawalsScript PlutusV3 single_cbor_hex "experiments/context-corpus/.work/hex/withdrawals_sum.hex"
#import_uplc proposalsScript PlutusV3 single_cbor_hex "experiments/context-corpus/.work/hex/proposals_deposit.hex"
#prep_uplc preparedWithdrawals withdrawalsScript viewArgs 10000
#prep_uplc preparedProposals proposalsScript viewArgs 10000
#check preparedWithdrawals.prop
#check preparedProposals.prop
open Lean
run_cmd do
  for name in [`preparedWithdrawals.prop, `preparedProposals.prop] do
    let info ← getConstInfo name
    let some value := info.value? | throwError "missing prepared definition"
    let constants := value.getUsedConstants
    if value.hasFVar || constants.contains `PlutusCore.UPLC.CekMachine.runSteps ||
        constants.contains `PlutusCore.UPLC.CekMachine.step then
      throwError "prepared fold is not a closed CEK-free summary"
  logInfo "both prep_uplc definitions are closed and CEK-free"
