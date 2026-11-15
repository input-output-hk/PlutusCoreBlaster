import ContextCorpus.Boundary
import PlutusCore.UPLC.CekMachine
import ContextCorpus.Fixtures

open ContextCorpus PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
set_option maxRecDepth 20000
set_option maxHeartbeats 0

-- Kernel-checked equality of the complete wire representation on one fixture.
-- Neither this fixture nor stdlib's placeholder is asserted ledger-valid.
theorem placeholder_wire_agrees :
    cekExecuteProgram corpusPlaceholderProgram.script [] 100 = .Halt (.VCon (.Data (encode empty))) := by
  rfl

#print axioms placeholder_wire_agrees
