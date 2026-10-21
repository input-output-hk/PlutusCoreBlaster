import PlutusCore.UPLC.BlueprintEncoding.Assurance
open PlutusCore.UPLC.BlueprintEncoding.Assurance
open PlutusCore.UPLC.BlueprintEncoding.Assurance.Internal
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Utils
open PlutusCore.UPLC.Term

-- An unfinished computation must satisfy neither success nor rejection.
example (p : Program) (args : List Term) : isExhausted (cekExecuteProgram p args 0) := by
  cases p; exact True.intro
example (p : Program) (args : List Term) : ¬ isErrorState (cekExecuteProgram p args 0) := by
  cases p; exact id
example : isHaltState (cekExecuteProgram (.Program (.Version 1 0 0) (.Const .Unit)) [] 10) := by
  exact True.intro

def malformed : String := "{\"$schema\":\"wrong\",\"preamble\":{},\"blueprint\":{},\"properties\":[]}"
#guard !(parseDocument malformed).isOk
