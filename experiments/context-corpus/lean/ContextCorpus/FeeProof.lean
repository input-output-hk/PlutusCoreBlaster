import Blaster
import ContextCorpus.Boundary
import ContextCorpus.Fixtures
import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.Optimize.Extension

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue ContextCorpus
set_option maxHeartbeats 0
set_option maxRecDepth 20000

-- Run validate.py first to generate the independent Aiken compilation.
#prep_uplc preparedFee corpusFeeProgram spendArgs 1000

-- A solver-backed calibration using the existing #prep_uplc/#blaster trust
-- model, not a kernel-reconstructed equivalence between .prop and .exec.
-- Every transaction field, redeemer and spending payload is free. This is
-- not yet the missing full isValidContext theorem for an arbitrary purpose.
#blaster (timeout: 10) [∀ (v : View) (ownId : PlutusCore.ByteString.ByteString)
    (ownIndex : Int) (datum : Option PlutusCore.Data.Data),
    (preparedFee.prop v ownId ownIndex datum = .Halt (.VCon .Unit)) ↔ v.fee ≤ 2000000]
