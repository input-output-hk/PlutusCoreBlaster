import PlutusCore.UPLC.CekMachine
import Lean

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term PlutusCore.UPLC.Builtins PlutusCore.Data

-- The refactor's equivalence theorems must be kernel proofs. In particular,
-- neither the existing budget termination sorry nor an SMT admission may enter.
open Lean in
run_cmd do
  for name in [``evalBuiltin_eq_reference, ``step_eq_reference, ``runSteps_eq_reference] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom in {name}: {ax}"

-- Symbolic payloads reduce through concrete wrappers without SMT.
example (n : Int) :
    step default (.Return [Frame.RightApplicationOfValue (.VBuiltin .UnIData [] (.One .ArgV))]
      (.VCon (.Data (.I n)))) = .Return [] (.VCon (.Integer n)) := by rfl

example (fields : List Data) (tag : Int) :
    evalBuiltin default [] .UnConstrData [.VCon (.Data (.Constr tag fields))] =
      .Return [] (.VCon (.Pair (.Integer tag, .ConstDataList fields))) := by rfl

-- Data destructors reject the wrong constructor, wrong CEK value, and arity.
example : evalBuiltin default [] .UnIData [.VCon (.Data (.List []))] = .Error := by rfl
example : evalBuiltin default [] .UnIData [.VCon (.Integer 4)] = .Error := by rfl
example : evalBuiltin default [] .UnIData [] = .Error := by rfl
example : evalBuiltin default [] .UnIData [.VCon (.Data (.I 4)), .VCon .Unit] = .Error := by rfl

-- The last live transition still consumes fuel: reaching Return is not Halt.
example (n : Int) : runSteps default (.Eval [] Environment.EmptyEnvironment (.Const (.Integer n))) 0 = .Error := by rfl
example (n : Int) : runSteps default (.Eval [] Environment.EmptyEnvironment (.Const (.Integer n))) 1 = .Error := by rfl
example (n : Int) : runSteps default (.Eval [] Environment.EmptyEnvironment (.Const (.Integer n))) 2 = .Halt (.VCon (.Integer n)) := by rfl
example (n : Int) : runSteps default (.Halt (.VCon (.Integer n))) 0 = .Halt (.VCon (.Integer n)) := by rfl
example : runSteps default .Error 0 = .Error := by rfl
