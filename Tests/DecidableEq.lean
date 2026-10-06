import PlutusCore.UPLC.CekMachine.DecidableEq
import PlutusCore.UPLC.CekMachine.Tests

namespace PlutusCore.UPLC.Term

example : DecidableEq Version := inferInstance
example : DecidableEq Program := inferInstance
example : (inferInstance : DecidableEq AtomicType) = instDecidableEqOfLawfulBEq := rfl

/-! ### `==` and `=` on `Term` -/

example : (Term.Lam Term.Error == Term.Lam (Term.Var 0)) = false := rfl

example : Term.Lam Term.Error ≠ Term.Lam (Term.Var 0) := by decide

example : Term.Lam Term.Error = Term.Lam Term.Error := by decide

-- These catch a second `BEq` taking precedence over the hand-written or derived one.
example : (inferInstance : BEq Const) = instBEqConst := rfl

example : (inferInstance : BEq Term) = instBEqTerm := rfl

example : (inferInstance : BEq BuiltinFun) = instBEqBuiltinFun := rfl

/-! ### A BLS12-381 constant, decided -/

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    = Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1 := by decide

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    ≠ Const.Bls12_381_G1_element .infinity := by decide

/-! ### Lawful `BEq` instances -/

example : LawfulBEq Const := inferInstance
example : LawfulBEq Term := inferInstance
example : LawfulBEq BuiltinFun := inferInstance
example : LawfulBEq AtomicType := inferInstance
example : LawfulBEq ExBudget.ExCPU := inferInstance
example : LawfulBEq ExBudget.ExMemory := inferInstance
example : LawfulBEq ExBudget.ExBudget := inferInstance
example : LawfulBEq Builtins.ExpectedBuiltinArg := inferInstance
example : LawfulBEq Builtins.ExpectedBuiltinArgs := inferInstance
example : LawfulBEq CekValue.CekValue := inferInstance

end PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue

example : DecidableEq Environment := inferInstance

end PlutusCore.UPLC.CekValue

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekValue

example : DecidableEq Stack := inferInstance
example : DecidableEq State := inferInstance
example : DecidableEq EvaluationResult := inferInstance

/-! ### `==` and `=` on values, frames and states -/

section
open PlutusCore.UPLC.Term

private def t1 : Term := .Lam .Error
private def t2 : Term := .Lam (.Var 0)

#guard t1 != t2
#guard [t1] != [t2]
#guard CekValue.VDelay t1 [] != CekValue.VDelay t2 []
#guard State.Eval [] [] t1 != State.Eval [] [] t2
#guard Frame.CaseScrutinee [t1] [] != Frame.CaseScrutinee [t2] []

example : CekValue.VDelay t1 [] ≠ CekValue.VDelay t2 [] := by decide
example : State.Eval [] [] t1 ≠ State.Eval [] [] t2 := by decide
example : Frame.CaseScrutinee [t1] [] ≠ Frame.CaseScrutinee [t2] [] := by decide

#guard CekValue.VCon (Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1)
    == CekValue.VCon (Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1)

#guard CekValue.VCon (Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1)
    != CekValue.VCon (Const.Bls12_381_G1_element .infinity)

end

/-! ### States that differ -/

example : stepN testSemanticsVariant testStart 1
    ≠ stepN testSemanticsVariant testStart 2 := by nofun

example : runSteps testSemanticsVariant testStart 1 ≠ State.Halt testResult := by
  intro h
  cases h

/-! ### At a realistic size -/

/-- `Force (Delay (Force (Delay ... testTerm)))`, `n` layers deep. -/
def deepTerm : Nat → PlutusCore.UPLC.Term.Term
  | 0 => testTerm
  | n + 1 => .Force (.Delay (deepTerm n))

/-- `n` distinct values, so no two entries can be confused for each other. -/
def bigEnv (n : Nat) : Environment :=
  (List.range n).map fun i => PlutusCore.UPLC.CekValue.CekValue.VCon
    (PlutusCore.UPLC.Term.Const.Integer (Int.ofNat i))

/-- `n` application frames, each awaiting a distinct `Var`. -/
def bigStack (n : Nat) : Stack :=
  (List.range n).map fun i => Frame.LeftApplicationToTerm (PlutusCore.UPLC.Term.Term.Var i) []

/-- A ten-frame stack, a thirty-entry environment, and a thirty-deep term. -/
def bigState : State := State.Eval (bigStack 10) (bigEnv 30) (deepTerm 30)

/-- `bigState` with the entry at index 29, the very last one, replaced. -/
def bigStateAlt : State :=
  State.Eval (bigStack 10)
    ((bigEnv 30).set 29 (PlutusCore.UPLC.CekValue.CekValue.VCon
      (PlutusCore.UPLC.Term.Const.Integer 999)))
    (deepTerm 30)

example : bigState = bigState := rfl
example : bigState ≠ bigStateAlt := by nofun

/-! ### Checks that need the instances -/

-- The body at each `n` is a state disequality, decided by `DecidableEq State`.
example : ∀ n, n < 4 → stepN testSemanticsVariant testStart n ≠ State.Error := by decide

-- `eraseDups` and `count` compare states through the `==` that `DecidableEq State` gives.
example : [bigState, bigStateAlt, bigState].eraseDups.length = 2 := by decide

example : ([bigState, bigStateAlt].count bigState) = 1 := by decide

end PlutusCore.UPLC.CekMachine
