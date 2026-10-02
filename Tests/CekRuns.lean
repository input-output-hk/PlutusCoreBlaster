import PlutusCore.UPLC.CekMachine.DecidableEq
import PlutusCore.UPLC.CekMachine.Tests

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekValue (CekValue)

-- On a non-terminal state `step` returns a different state.
example : step testSemanticsVariant testStart ≠ testStart := by nofun

-- Index two on the `testStart` run is terminal, and no earlier index is.
example : terminal (stepN testSemanticsVariant testStart 2) := by decide

example : ∀ i, i < 2 → ¬ terminal (stepN testSemanticsVariant testStart i) := by decide

-- The state at two is the state at every later index.
example (m : Nat) :
    stepN testSemanticsVariant testStart (2 + m)
      = stepN testSemanticsVariant testStart 2 :=
  stepN_fix testSemanticsVariant testStart 2 (by decide) m

/-! ### A `Data` constant through the machine -/

section
open PlutusCore.UPLC.Term

/-- A `Data` payload with a `Constr`, an `I`, a `B` and a nested `List`. -/
def testData : PlutusCore.Data.Data := .Constr 0 [.I 1, .B "ab", .List [.I 2]]

def dataTerm : Term := .Force (.Delay (.Const (.Data testData)))

/-- The unevaluated starting state for `testData`. -/
def testDataStart : State := State.Eval [] [] dataTerm

/-- The first `n` states of the run from `testDataStart`. -/
def dataTrace (n : Nat) : List State :=
  (List.range n).map (stepN testSemanticsVariant testDataStart)

/-- The run halts after five steps, on the `Data` constant inside the `Delay`. -/
theorem dataTrace_halts : stepN testSemanticsVariant testDataStart 5
    = State.Halt (CekValue.VCon (Const.Data testData)) := by decide

-- The first six states are distinct.
example : (dataTrace 6).Nodup := by decide

-- No index before five on this run is terminal.
example : ∀ i, i < 5 → ¬ terminal (stepN testSemanticsVariant testDataStart i) := by decide

-- The state at five and at every later index is halted on the `Data` constant.
example (m : Nat) :
    stepN testSemanticsVariant testDataStart (5 + m)
      = State.Halt (CekValue.VCon (Const.Data testData)) :=
  (stepN_fix testSemanticsVariant testDataStart 5 (by decide) m).trans dataTrace_halts

def dataProgram : Program :=
  Program.Program (Version.Version 1 1 0) dataTerm

-- One step short of enough fuel the program is an `Error`.
example : cekExecuteProgramWithSemanticVariant testSemanticsVariant dataProgram [] 4
    = State.Error := by decide

-- At five and at every larger fuel the program halts on the `Data` constant.
example : cekExecuteProgramWithSemanticVariant testSemanticsVariant dataProgram [] 5
    = State.Halt (CekValue.VCon (Const.Data testData)) := by decide

example (m : Nat) :
    cekExecuteProgramWithSemanticVariant testSemanticsVariant dataProgram [] (5 + m)
      = State.Halt (CekValue.VCon (Const.Data testData)) :=
  cekExecuteProgramWithSemanticVariant_halt_stable testSemanticsVariant dataProgram []
    (CekValue.VCon (Const.Data testData)) 5 m (by decide)

def equalsDataTerm : Term :=
  .Apply (.Apply (.Builtin .EqualsData) (.Const (.Data testData))) (.Const (.Data testData))

/-- The unevaluated starting state for `equalsDataTerm`. -/
def equalsDataStart : State := State.Eval [] [] equalsDataTerm

-- At index ten the builtin has halted on `true`.
example : stepN testSemanticsVariant equalsDataStart 10
    = State.Halt (CekValue.VCon (Const.Bool true)) := by decide

/-- `testData` with the entry of its nested `List` changed. -/
def neqData : PlutusCore.Data.Data := .Constr 0 [.I 1, .B "ab", .List [.I 3]]

def neqDataTerm : Term :=
  .Apply (.Apply (.Builtin .EqualsData) (.Const (.Data testData))) (.Const (.Data neqData))

/-- The unevaluated starting state for `neqDataTerm`. -/
def neqDataStart : State := State.Eval [] [] neqDataTerm

-- At index ten the builtin has halted on `false`.
example : stepN testSemanticsVariant neqDataStart 10
    = State.Halt (CekValue.VCon (Const.Bool false)) := by decide

-- None of the first eleven states of the `equalsDataStart` run is an `Error`.
example : ∀ n, n < 11 → stepN testSemanticsVariant equalsDataStart n ≠ State.Error := by decide

end

end PlutusCore.UPLC.CekMachine
