import PlutusCore.UPLC.CekMachine.Lemmas

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)

/-! ## Concrete checks for the iteration of `step`. -/

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

-- `stepN` really iterates.
example : stepN testSemanticsVariant testStart 1
    = State.Return [] testResult := rfl
example : stepN testSemanticsVariant testStart 2
    = State.Halt testResult := rfl

-- `step` returns a `Halt` state and `State.Error` unchanged.
example (V : CekValue) :
    step testSemanticsVariant (State.Halt V) = State.Halt V := rfl
example : step testSemanticsVariant State.Error = State.Error := rfl

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

-- One step short of enough fuel the program is an `Error`, and past enough the halt
-- result does not change.
def testProgram : PlutusCore.UPLC.Term.Program :=
  PlutusCore.UPLC.Term.Program.Program (PlutusCore.UPLC.Term.Version.Version 1 1 0) testTerm

example : cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] 1
    = State.Error := rfl
example (m : Nat) :
    cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] (2 + m)
      = State.Halt testResult :=
  cekExecuteProgramWithSemanticVariant_halt_stable testSemanticsVariant testProgram []
    testResult 2 m rfl

end PlutusCore.UPLC.CekMachine
