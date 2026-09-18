import PlutusCore.UPLC.CekMachine.DecidableEq
import PlutusCore.UPLC.CekMachine.Lemmas

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue Environment)

/-! ## Concrete checks for the exhaustion-free iteration

Closed equations close by `rfl`, and closed disequalities by `cases` or `nofun`, neither
needing an instance. -/

def testSemanticsVariant : BuiltinSemanticsVariant :=
  PlutusCore.Default.Internal.BuiltinSemanticsVariant.defaultFunSemanticsVariantB

/-- A constant, which the machine evaluates in exactly two steps. -/
def testTerm : PlutusCore.UPLC.Term.Term :=
  PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Integer 42)

/-- The unevaluated starting state for `testTerm`. -/
def testStart : State := State.Eval [] [] testTerm

/-- Where `testTerm` ends up. -/
def testResult : CekValue :=
  PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 42)

-- `stepN` really iterates. Without these, every check below would pass against a
-- `stepN` that never stepped.
example : stepN testSemanticsVariant testStart 1
    = State.Return [] testResult := rfl
example : stepN testSemanticsVariant testStart 2
    = State.Halt testResult := rfl
example : stepN testSemanticsVariant testStart 1
    ≠ stepN testSemanticsVariant testStart 2 := by nofun

-- Past the halt it sits still.
example : stepN testSemanticsVariant testStart 5
    = State.Halt testResult := rfl
example (V : CekValue) :
    stepAbs testSemanticsVariant (State.Halt V) = State.Halt V := rfl
example : stepAbs testSemanticsVariant State.Error = State.Error := rfl

-- At zero fuel `stepN` is the identity.
example (s : State) : stepN testSemanticsVariant s 0 = s := rfl

-- Splitting through `runSteps` turns a halting run into an `Error`. Splitting
-- through `stepN` does not.
example : runSteps testSemanticsVariant testStart 1 = State.Error := rfl
example : runSteps testSemanticsVariant testStart 2
    = State.Halt testResult := rfl
example :
    runSteps testSemanticsVariant (runSteps testSemanticsVariant testStart 1) 1
      = State.Error := rfl
example :
    runSteps testSemanticsVariant (stepN testSemanticsVariant testStart 1) 1
      = State.Halt testResult := rfl

-- The composition lemma at a concrete split.
example (s : State) :
    runSteps testSemanticsVariant s (2 + 3)
      = runSteps testSemanticsVariant (stepN testSemanticsVariant s 2) 3 :=
  runSteps_add testSemanticsVariant s 2 3

-- The stability theorem is about programs that really do halt, and fuel really does
-- matter for them: one step short of enough is an `Error`.
def testProgram : PlutusCore.UPLC.Term.Program :=
  PlutusCore.UPLC.Term.Program.Program (PlutusCore.UPLC.Term.Version.Version 1 1 0) testTerm

example : cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] 1
    = State.Error := rfl
example : cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] 2
    = State.Halt testResult := rfl
example : cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] (2 + 7)
    = State.Halt testResult := rfl

/-! ### States that differ -/

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
