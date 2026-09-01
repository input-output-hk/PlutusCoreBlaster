import PlutusCore.UPLC.CekMachine.Lemmas

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)

/-! ## Concrete checks for the fuel-free iteration

`rfl` rather than `native_decide`, since `State` has no `DecidableEq` instance. -/

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

end PlutusCore.UPLC.CekMachine
