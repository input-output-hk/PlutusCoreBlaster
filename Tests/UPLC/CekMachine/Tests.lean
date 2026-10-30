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

-- The assurance runner preserves the unfinished state one step before halting.
def testProgram : PlutusCore.UPLC.Term.Program :=
  PlutusCore.UPLC.Term.Program.Program (PlutusCore.UPLC.Term.Version.Version 1 1 0) testTerm

example : cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] 1
    = State.Return [] testResult := rfl
example (m : Nat) :
    cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] (2 + m)
      = State.Halt testResult :=
  cekExecuteProgramWithSemanticVariant_halt_stable testSemanticsVariant testProgram []
    testResult 2 m rfl

/-! ## Costs

At variant B every step costs 16000 CPU and 100 memory, and the startup cost is 100 of each. -/

open PlutusCore.UPLC.ExBudget (ExBudget)

/-- `⟨⟨cpu⟩, ⟨mem⟩⟩` -/
def testBudget (cpu mem : Nat) : ExBudget := ⟨⟨cpu⟩, ⟨mem⟩⟩

-- One `Eval` step is charged, the `Return` to the empty stack is free.
example : runStepsWithCost testSemanticsVariant testStart 2
    = (State.Halt testResult, testBudget 16000 100) := rfl
-- Past the halt, no more cost.
example : runStepsWithCost testSemanticsVariant testStart 5
    = (State.Halt testResult, testBudget 16000 100) := rfl
-- Unlike `runSteps`, out of steps it hands back the state reached.
example : runStepsWithCost testSemanticsVariant testStart 1
    = (State.Return [] testResult, testBudget 16000 100) := rfl
-- Evaluating `error` is free.
example : runStepsWithCost testSemanticsVariant (State.Eval [] [] .Error) 5
    = (State.Error, ExBudget.zero) := rfl

-- A program pays the startup cost on top.
example : cekExecuteProgramWithCost testSemanticsVariant testProgram [] 2
    = (State.Halt testResult, testBudget 16100 200) := rfl

-- Judged against a budget: exactly enough, one unit short in each resource, out of steps
-- within budget (inconclusive), and out of steps having already overspent.
example : EvaluationResult.ofCostedRun (testBudget 16100 200)
    (cekExecuteProgramWithCost testSemanticsVariant testProgram [] 2)
    = .Success testResult (testBudget 16100 200) := rfl
example : EvaluationResult.ofCostedRun (testBudget 16099 200)
    (cekExecuteProgramWithCost testSemanticsVariant testProgram [] 2)
    = .BudgetExhausted (testBudget 0 0) := rfl
example : EvaluationResult.ofCostedRun (testBudget 16100 199)
    (cekExecuteProgramWithCost testSemanticsVariant testProgram [] 2)
    = .BudgetExhausted (testBudget 0 0) := rfl
example : EvaluationResult.ofCostedRun (testBudget 16100 200)
    (cekExecuteProgramWithCost testSemanticsVariant testProgram [] 1)
    = .StepLimitReached (testBudget 16100 200) := rfl
example : EvaluationResult.ofCostedRun (testBudget 100 100)
    (cekExecuteProgramWithCost testSemanticsVariant testProgram [] 1)
    = .BudgetExhausted (testBudget 0 0) := rfl

def testProgramOf (t : PlutusCore.UPLC.Term.Term) : PlutusCore.UPLC.Term.Program :=
  PlutusCore.UPLC.Term.Program.Program (PlutusCore.UPLC.Term.Version.Version 1 0 0) t

-- A builtin's cost depends on its arguments' sizes, so these are evaluated rather than reduced.
-- `[[(builtin addInteger) (con integer 1)] (con integer 1)]` costs what the conformance test
-- `builtin/semantics/addInteger/addInteger-01` expects: 181308 CPU, 602 memory.
#guard consumed? (cekExecuteProgramWithBudget
    (testProgramOf (.Apply (.Apply (.Builtin .AddInteger) (.Const (.Integer 1))) (.Const (.Integer 1))))
    .plutusV3 .postConway [] (testBudget 1000000 1000) 100)
  == some (testBudget 181308 602)

-- Forcing a builtin that awaits a term argument is an error, and the builtin is not charged:
-- only the four steps and the startup cost are.
#guard isEvaluationError (cekExecuteProgramWithBudget
    (testProgramOf (.Force (.Apply (.Builtin .AddInteger) (.Const (.Integer 1)))))
    .plutusV3 .postConway [] (testBudget 1000000 1000) 100)
#guard (cekExecuteProgramWithCost .defaultFunSemanticsVariantE
    (testProgramOf (.Force (.Apply (.Builtin .AddInteger) (.Const (.Integer 1))))) [] 100).2
  == testBudget 64100 500

end PlutusCore.UPLC.CekMachine
