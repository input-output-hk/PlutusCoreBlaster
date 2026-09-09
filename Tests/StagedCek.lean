import PlutusCore.UPLC.PreProcess

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue
namespace Tests.StagedCek

def identity : PlutusScript :=
  ⟨.PlutusV3, .Program (.Version 1 1 0) (.Lam "x" (.Var 0))⟩

def unitInput : List Term := [.Const .Unit]

#prep_uplc ordinary identity unitInput 7
section
set_option plutuscore.stagedCek true
#prep_uplc fused identity unitInput 7
#prep_uplc exhausted identity unitInput 6
end

-- The option affects only preparation; both executables retain the reference.
example : fused.exec = cekExecuteProgram identity.script unitInput 7 := rfl
example : ordinary.exec = fused.exec := rfl
example : ordinary.prop = State.Halt (.VCon .Unit) := rfl
example : fused.prop = State.Halt (.VCon .Unit) := rfl
example : exhausted.prop = State.Error := rfl

run_cmd do
  if plutuscore.stagedCek.get (← Lean.getOptions) then
    throwError "staged CEK option escaped its section"

end Tests.StagedCek
