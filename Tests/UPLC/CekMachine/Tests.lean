import PlutusCore.UPLC.CekMachine.Lemmas

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)

/-! ## Concrete checks for the iteration of `step`. -/

def testSemanticsVariant : BuiltinSemanticsVariant :=
  PlutusCore.Default.Internal.BuiltinSemanticsVariant.defaultFunSemanticsVariantB

def testProtocolVersion : ProtocolVersion :=
  PlutusCore.Default.Internal.ProtocolVersion.postVanRossem

/-- A constant, which the machine evaluates in exactly two steps. -/
def testTerm : PlutusCore.UPLC.Term.Term :=
  PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Integer 42)

/-- The unevaluated starting state for `testTerm`. -/
def testStart : State := State.Eval [] [] testTerm

/-- Where `testTerm` ends up. -/
def testResult : CekValue :=
  PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 42)

-- `stepN` really iterates.
example : stepN testSemanticsVariant testProtocolVersion testStart 1
    = State.Return [] testResult := rfl
example : stepN testSemanticsVariant testProtocolVersion testStart 2
    = State.Halt testResult := rfl

-- `step` returns a `Halt` state and `State.Error` unchanged.
example (V : CekValue) :
    step testSemanticsVariant testProtocolVersion (State.Halt V) = State.Halt V := rfl
example : step testSemanticsVariant testProtocolVersion State.Error = State.Error := rfl

-- At zero fuel `stepN` is the identity.
example (s : State) : stepN testSemanticsVariant testProtocolVersion s 0 = s := rfl

-- Splitting through `runSteps` turns a halting run into an `Error`. Splitting
-- through `stepN` does not.
example : runSteps testSemanticsVariant testProtocolVersion testStart 1 = State.BudgetExhausted := rfl
example : runSteps testSemanticsVariant testProtocolVersion testStart 2
    = State.Halt testResult := rfl
example :
    runSteps testSemanticsVariant testProtocolVersion (runSteps testSemanticsVariant testProtocolVersion testStart 1) 1
      = State.BudgetExhausted := rfl
example :
    runSteps testSemanticsVariant testProtocolVersion (stepN testSemanticsVariant testProtocolVersion testStart 1) 1
      = State.Halt testResult := rfl

-- The assurance runner preserves the unfinished state one step before halting.
def testProgram : PlutusCore.UPLC.Term.Program :=
  PlutusCore.UPLC.Term.Program.Program (PlutusCore.UPLC.Term.Version.Version 1 1 0) testTerm

example : cekExecuteStateRetention testSemanticsVariant testProtocolVersion testProgram [] 1
    = State.Return [] testResult := rfl

example (m : Nat) :
    cekExecuteProgramWithSemanticVariant testSemanticsVariant testProtocolVersion testProgram [] (2 + m)
      = State.Halt testResult :=
  cekExecuteProgramWithSemanticVariant_halt_stable testSemanticsVariant testProtocolVersion testProgram []
    testResult 2 m rfl

end PlutusCore.UPLC.CekMachine
