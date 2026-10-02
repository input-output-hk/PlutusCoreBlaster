import PlutusCore.UPLC.CekMachine.DecidableEq
import PlutusCore.UPLC.CekMachine.Tests
import PlutusCore.UPLC.Term.DecidableEq

namespace PlutusCore.UPLC.Term

example : DecidableEq Version := inferInstance
example : DecidableEq Program := inferInstance

/-! ### The two equalities on `Term` -/

example : (Term.Lam "x" Term.Error == Term.Lam "y" Term.Error) = true := rfl

example : Term.Lam "x" Term.Error ≠ Term.Lam "y" Term.Error := by decide

example : Term.Lam "x" Term.Error = Term.Lam "x" Term.Error := by decide

-- These catch a second `BEq Const` or `BEq Term` taking precedence over the hand-written ones.
example : (inferInstance : BEq Const) = instBEqConst := rfl

example : (inferInstance : BEq Term) = instBEqTerm := rfl

/-! ### A BLS12-381 constant, decided

`==` sends these through the `opaque` `bls12_381_G1_equal`, which does not reduce.
`Const.decEq` compares the underlying `Point`, which does. -/

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    = Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1 := by decide

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    ≠ Const.Bls12_381_G1_element .infinity := by decide

/-! ### `LawfulBEq Const` does not synthesize -/

/-- error: failed to synthesize
  LawfulBEq Const

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth LawfulBEq Const

end PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue

example : DecidableEq Environment := inferInstance

end PlutusCore.UPLC.CekValue

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekValue

example : DecidableEq Stack := inferInstance
example : DecidableEq State := inferInstance
example : DecidableEq EvaluationResult := inferInstance

/-! ### The two equalities on values, frames and states -/

section
open PlutusCore.UPLC.Term

private def t1 : Term := .Lam "x" .Error
private def t2 : Term := .Lam "y" .Error

#guard t1 == t2
#guard [t1] == [t2]
#guard CekValue.VDelay t1 [] == CekValue.VDelay t2 []
#guard State.Eval [] [] t1 == State.Eval [] [] t2
#guard Frame.CaseScrutinee [t1] [] == Frame.CaseScrutinee [t2] []

example : CekValue.VDelay t1 [] ≠ CekValue.VDelay t2 [] := by decide
example : State.Eval [] [] t1 ≠ State.Eval [] [] t2 := by decide
example : Frame.CaseScrutinee [t1] [] ≠ Frame.CaseScrutinee [t2] [] := by decide

-- `==` on a BLS constant runs but does not reduce, so these are guards rather than `decide` examples.
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

-- `eraseDups` and `count` compare states through `instBEqState`.
example : [bigState, bigStateAlt, bigState].eraseDups.length = 2 := by decide

example : ([bigState, bigStateAlt].count bigState) = 1 := by decide

end PlutusCore.UPLC.CekMachine
