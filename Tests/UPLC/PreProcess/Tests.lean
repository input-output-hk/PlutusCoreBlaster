import PlutusCore.UPLC.PreProcess

namespace PlutusCore.UPLC.PreProcess

open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.PlutusScript (PlutusScript)

/-! ## `#prep_uplc` without an input conversion function

The program is then run on no arguments (`[]`). This form used to fail with
"incorrect number of universe levels" because `List.nil` was built without its level. -/

/-- A closed program: the constant 42, which the machine evaluates in exactly two steps. -/
def preProcessTestScript : PlutusScript :=
  { lang := .PlutusV3
    script := PlutusCore.UPLC.Term.Program.Program (PlutusCore.UPLC.Term.Version.Version 1 1 0)
      (PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Integer 42)) }

-- `#prep_uplc` declares its names at the root, whatever the enclosing namespace.
#prep_uplc preProcessTestNoInputs preProcessTestScript 10

-- The optimizer evaluates the closed program completely.
example : preProcessTestNoInputs.prop
    = State.Halt (CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 42)) := rfl
example : preProcessTestNoInputs.exec
    = State.Halt (CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 42)) := rfl

end PlutusCore.UPLC.PreProcess
