import Blaster
import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.PlutusScript
import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.Utils

namespace PlutusCore.UPLC.CekMachine.Tests

open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils

set_option warn.sorry false
-- `blaster` closes a `Valid` goal with `admit`

/-- `(con c)`.  NOTE: spelled out because `Term.Const` resolves to the *type*
    `Const` inside the `PlutusCore.UPLC` namespace. -/
private def con (c : Const) : Term := .Const c

private def t0 : Term := con (.Integer 10)
private def t1 : Term := con (.Integer 20)
private def t2 : Term := con (.Integer 30)

/-! ## `case` branch selection -/

example : caseBranch []       0    = none    := rfl
example : caseBranch [t0, t1] 0    = some t0 := rfl
example : caseBranch [t0, t1] 1    = some t1 := rfl
example : caseBranch [t0, t1] 2    = none    := rfl
example : caseBranch [t0, t1] (-1) = none    := rfl
example : caseBranch [t0, t1] (-9) = none    := rfl

/-! ## `case` evaluation

    Which branch a `case` selects, and when it is a machine error, must not
    depend on how the `Frame.CaseScrutinee` rule is written down.
-/

private def run (t : Term) : Option Integer :=
  fromFrameToInt (cekExecuteProgram (Program.Program (Version.Version 1 1 0) t) [] 50)

private def isError (t : Term) : Bool :=
  match cekExecuteProgram (Program.Program (Version.Version 1 1 0) t) [] 50 with
  | State.Error => true
  | _           => false

private def lte (a b : Integer) : Term :=
  ((Term.Builtin BuiltinFun.LessThanEqualsInteger).Apply (con (.Integer a))).Apply (con (.Integer b))

-- scrutinee is a builtin `Bool`: `False` takes branch 0, `True` takes branch 1,
-- and `False` is also accepted with a single branch
example : run ((lte 3 5).Case [t0, t1]) = some 20 := by native_decide
example : run ((lte 5 3).Case [t0, t1]) = some 10 := by native_decide
example : run ((lte 5 3).Case [t0])     = some 10 := by native_decide
example : isError ((lte 3 5).Case [t0])         = true := by native_decide
example : isError ((lte 3 5).Case [t0, t1, t2]) = true := by native_decide
example : isError ((lte 5 3).Case [t0, t1, t2]) = true := by native_decide
example : isError ((lte 5 3).Case [])           = true := by native_decide

-- scrutinee is a constant `Integer`: it indexes the branch list, and a negative
-- or out-of-range tag is an error
example : run ((con (.Integer 0)).Case [t0, t1, t2]) = some 10 := by native_decide
example : run ((con (.Integer 1)).Case [t0, t1, t2]) = some 20 := by native_decide
example : run ((con (.Integer 2)).Case [t0, t1, t2]) = some 30 := by native_decide
example : isError ((con (.Integer 3)).Case [t0, t1, t2])    = true := by native_decide
example : isError ((con (.Integer (-1))).Case [t0, t1, t2]) = true := by native_decide
example : isError ((con (.Integer 0)).Case [])              = true := by native_decide

-- scrutinee is a constant `Unit`: exactly one branch, taking no arguments
example : run ((con .Unit).Case [t0]) = some 10 := by native_decide
example : isError ((con .Unit).Case [])       = true := by native_decide
example : isError ((con .Unit).Case [t0, t1]) = true := by native_decide

-- scrutinee is a constant list: a cons applies branch 0 to head and tail,
-- an empty list takes branch 1
private def intList (cs : List Integer) : Term := con (.ConstList (cs.map Const.Integer))

/-- `(lam h (lam t h))`: keeps the head of the matched list -/
private def headBranch : Term := Term.Lam "h" (Term.Lam "t" (Term.Var 1))

example : run ((intList [7, 8]).Case [headBranch, t0]) = some 7  := by native_decide
example : run ((intList [7, 8]).Case [headBranch])     = some 7  := by native_decide
example : run ((intList []).Case [headBranch, t0])     = some 10 := by native_decide
example : isError ((intList []).Case [headBranch])             = true := by native_decide
example : isError ((intList [7, 8]).Case [headBranch, t0, t2]) = true := by native_decide

-- scrutinee is a `constr` term: the constructor tag indexes the branch list
example : run ((Term.Constr 1 []).Case [t0, t1, t2])     = some 20 := by native_decide
example : isError ((Term.Constr 3 []).Case [t0, t1, t2]) = true    := by native_decide

/-! ## Regression: `blaster` must see through a `case`

    A `case` whose scrutinee is symbolic used to leave the whole
    `Frame.CaseScrutinee` match unreduced, which made `blaster` diverge on any
    program the Scalus compiler emits for PlutusV3.  See
    `PlutusCore.UPLC.CekMachine.caseBranch`.
-/

private def script (t : Term) : PlutusScript :=
  { lang := PlutusLanguage.PlutusV3, script := Program.Program (Version.Version 1 1 0) t }

/-- `(lam x (lam y (case [(builtin lessThanEqualsInteger) x y] y x)))`, i.e. `min x y`
    the way the Scalus compiler lowers it for PlutusV3. -/
def minCaseScript : PlutusScript :=
  script (Term.Lam "x" (Term.Lam "y"
    ((((Term.Builtin BuiltinFun.LessThanEqualsInteger).Apply (Term.Var 1)).Apply
        (Term.Var 0)).Case [Term.Var 0, Term.Var 1])))

/-- `(lam x (case x [(con integer 10) (con integer 20)]))`: a `case` on a symbolic
    integer tag, the shape an ADT match lowers to. -/
def intCaseScript : PlutusScript :=
  script (Term.Lam "x" ((Term.Var 0).Case [t0, t1]))

private def oneInteger  (x : Integer)   : List Term := [con (.Integer x)]
private def twoIntegers (x y : Integer) : List Term := [con (.Integer x), con (.Integer y)]

#prep_uplc minCasePrep minCaseScript twoIntegers 30
#prep_uplc intCasePrep intCaseScript oneInteger 15

theorem minCase_is_a_lower_bound : ∀ (x y r : Integer),
  (fromFrameToInt $ minCasePrep.prop x y) = some r → r ≤ x ∧ r ≤ y := by blaster

theorem intCase_selects_a_branch : ∀ (x r : Integer),
  (fromFrameToInt $ intCasePrep.prop x) = some r → r = 10 ∨ r = 20 := by blaster

end PlutusCore.UPLC.CekMachine.Tests
