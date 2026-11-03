import PlutusCore.UPLC
import Blaster

namespace DropListTwoPrograms

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Utils
open PlutusCore.Data (Data)
open PlutusCore.UPLC.PlutusScript (PlutusScript)

/-- Length guard: halts with `True` iff `xs` has exactly 2 elements.

Program:
`(lam xs [ (force (builtin nullList)) [ (force (builtin tailList)) [ (force (builtin tailList)) xs ] ] ])`
-/
def lengthGuard : PlutusScript :=
  { lang := .PlutusV3
    script := singleCborEncodedScriptFromHexM "4d0101002357466ae88d5d100081" }

/-- Read with `dropList`: drops the first 2 elements of `xs` and tests emptiness.

Program:
`(lam xs [ (force (builtin nullList)) [ (force (builtin dropList)) (con integer 2) xs ] ])`
-/
def readWithDropList : PlutusScript :=
  { lang := .PlutusV3
    script := singleCborEncodedScriptFromHexM "4d01010023574666af6120040011" }

/-- Read with `tailList` steps: the same program as `lengthGuard`.

Program:
`(lam xs [ (force (builtin nullList)) [ (force (builtin tailList)) [ (force (builtin tailList)) xs ] ] ])`
-/
def readWithTails : PlutusScript :=
  { lang := .PlutusV3
    script := singleCborEncodedScriptFromHexM "4d0101002357466ae88d5d100081" }

def listInput (xs : List Data) : List Term := [Term.Const (Const.ConstDataList xs)]

#prep_uplc appliedGuard lengthGuard listInput 100
#prep_uplc appliedDropList readWithDropList listInput 100
#prep_uplc appliedTails readWithTails listInput 100

-- The guard and the read both take tails.
#blaster (gen-cex: 1) [
  ∀ (xs : List Data),
    appliedGuard.prop xs = State.Halt (CekValue.VCon (Const.Bool true)) →
    appliedTails.prop xs = State.Halt (CekValue.VCon (Const.Bool true))]

-- The guard takes tails, the read `dropList`.
#blaster (gen-cex: 1) [
  ∀ (xs : List Data),
    appliedGuard.prop xs = State.Halt (CekValue.VCon (Const.Bool true)) →
    appliedDropList.prop xs = State.Halt (CekValue.VCon (Const.Bool true))]

end DropListTwoPrograms
