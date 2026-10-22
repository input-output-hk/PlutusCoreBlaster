import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.ScriptEncoding.Basic

namespace PlutusCore.UPLC.PreProcess

open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.PlutusScript (PlutusScript)
open PlutusCore.UPLC.ExBudget (ExBudget)

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

/-! ## `#prep_uplc_with_cost`

The constant costs the startup cost and one step under the PlutusV3 cost model: 16100 CPU and 200 memory. -/

#prep_uplc_with_cost preProcessTestCost preProcessTestScript 10

example : preProcessTestCost.prop
    = (State.Halt (CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 42)), ⟨⟨16100⟩, ⟨200⟩⟩) := rfl
example : preProcessTestCost.exec
    = (State.Halt (CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 42)), ⟨⟨16100⟩, ⟨200⟩⟩) := rfl

/-! `saturate x = x * (x + 1)` by a loop that runs `x` times, `60 + 72 * x` steps. The cost of each
`subtractInteger`, `addInteger` and `multiplyInteger` depends on the size of the symbolic `x`.
150 steps cover `x ≤ 1`. -/

#import_uplc preProcessSaturate PlutusV3 textual "Benchmark/PrepUplc/Scripts/saturate.uplc"

def preProcessIntegerArg (x : PlutusCore.Integer.Integer) : List PlutusCore.UPLC.Term.Term :=
  [.Const (.Integer x)]

#prep_uplc_with_cost preProcessSaturateCost preProcessSaturate preProcessIntegerArg 150

#guard match preProcessSaturateCost.exec 1 with
  | (State.Halt (CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 2)), _) => true
  | _ => false
-- Out of steps at `x = 2`: the state reached is not `Halt`.
#guard match preProcessSaturateCost.exec 2 with
  | (State.Halt _, _) => false
  | _ => true

end PlutusCore.UPLC.PreProcess
