import ContextCorpus.Boundary
import ContextCorpus.CountFixtures
import PlutusCore.UPLC.Optimize.ListConsumer
import PlutusCore.UPLC.Optimize.Fold
import Lean.Util.CollectAxioms

namespace ContextCorpus.CountProperties
open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.Optimize
open PlutusCore.Data (Data)

set_option maxHeartbeats 2000000
set_option Elab.async false
set_option pp.maxSteps 2000
set_option maxRecDepth 20000

/-- Every transaction field, redeemer and spending payload is free. -/
structure Parameters where
  context : View
  ownId : PlutusCore.ByteString.ByteString
  ownIndex : Int
  datum : Option Data

def args (p : Parameters) := spendArgs p.context p.ownId p.ownIndex p.datum

inductive Case where
  | inputs | outputs | certificates | proposals

def script : Case → PlutusScript
  | .inputs => corpusInputsCount
  | .outputs => corpusOutputsCount
  | .certificates => corpusCertificatesCount
  | .proposals => corpusProposalsCount

def contextElements : Case → View → List Data
  | .inputs, v => v.inputs
  | .outputs, v => v.outputs
  | .certificates, v => v.certificates
  | .proposals, v => v.proposals

def elements (c : Case) (p : Parameters) : List Data := contextElements c p.context

def prefixCost : Case → Nat
  | .inputs => 202
  | .outputs => 210
  | .certificates => 222
  | .proposals => 257

def postCost : Case → Nat
  | .proposals => 13
  | _ => 16

def test : Case → Int → Bool
  | .inputs, n => n ≤ 4
  | .outputs, n => n ≤ 8
  | .certificates, n => n ≤ 3
  | .proposals, n => 0 < n

def start (c : Case) (p : Parameters) : State :=
  initialState (applyParams (script c).script.2 (args p))

def boundary (c : Case) (p : Parameters) : State :=
  runStepsPreservingState default (start c p) (prefixCost c)

def captures : State → PlutusCore.UPLC.CekValue.Environment
  | .Eval _ (_ :: _ :: env) _ => env
  | _ => []

def stack : State → Stack
  | .Eval k _ _ => k
  | _ => []

local macro "finite_reduce" : tactic =>
  `(tactic| simp_all [captures, stack, boundary, prefixCost, start, script, args,
    spendArgs, viewArgs, rawArgs, encode, corpusInputsCount, corpusOutputsCount,
    corpusCertificatesCount, corpusProposalsCount, initialState, applyParams,
    runStepsPreservingState, step, step.folding, evalBuiltin,
    PlutusCore.UPLC.Builtins.expectedArgs, List.get?Internal,
    PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.Data.unConstrData,
    PlutusCore.UPLC.BuiltinFunctions.Data.unIData,
    PlutusCore.UPLC.BuiltinFunctions.Data.unListData,
    PlutusCore.UPLC.BuiltinFunctions.List.headList,
    PlutusCore.UPLC.BuiltinFunctions.List.tailList,
    PlutusCore.UPLC.BuiltinFunctions.Pair.fstPair,
    PlutusCore.UPLC.BuiltinFunctions.Pair.sndPair,
    PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
    PlutusCore.UPLC.BuiltinFunctions.Integer.equalsInteger,
    PlutusCore.Bool.ifThenElse, PlutusCore.Integer.equalsInteger,
    PlutusCore.List.headList, PlutusCore.List.tailList,
    PlutusCore.Pair.fstPair, PlutusCore.Pair.sndPair])

def bindings (c : Case) (p : Parameters) : ListLength.Bindings where
  env := captures (boundary c p)
  chooseIndex := 10
  tailIndex := 12
  chooseBound := by
    cases c <;> finite_reduce
  tailBound := by
    cases c <;> finite_reduce

def argumentEnv : Stack → PlutusCore.UPLC.CekValue.Environment
  | _ :: .LeftApplicationToTerm _ env :: _ => env
  | _ => []

def guardEnv : Stack → PlutusCore.UPLC.CekValue.Environment
  | _ :: _ :: .ConstructorArgument _ _ _ (_ :: env) :: _ => env
  | _ :: .ConstructorArgument _ _ _ (_ :: env) :: _ => env
  | _ => []

def expectedStack (c : Case) (p : Parameters) : Stack :=
  let k := stack (boundary c p)
  match c with
  | .inputs => ListConsumer.leStack (argumentEnv k) (guardEnv k) (.Force .Error) 4
  | .outputs => ListConsumer.leStack (argumentEnv k) (guardEnv k) (.Force .Error) 8
  | .certificates => ListConsumer.leStack (argumentEnv k) (guardEnv k) (.Force .Error) 3
  | .proposals => ListConsumer.positiveStack (guardEnv k) (.Force .Error)

theorem stack_shape (c : Case) (p : Parameters) :
    stack (boundary c p) = expectedStack c p := by
    cases c <;>
      simp only [expectedStack, ListConsumer.leStack, ListConsumer.positiveStack,
        ListConsumer.guardStack, argumentEnv, guardEnv] <;> finite_reduce

/-- The only program-specific proof work is finite prefix/consumer reduction.
    All four programs share the same loop and its unbounded induction. -/
def certificate (c : Case) : ListConsumer.Certificate default Parameters where
  entry := start c
  elements := elements c
  bindings := bindings c
  stack := fun p => stack (boundary c p)
  prefixCost := prefixCost c
  postCost := postCost c
  test := test c
  prefixProof := by
    intro p
    cases c <;>
      simp only [ListLength.entry, ListLength.body, bindings, elements, contextElements] <;>
      finite_reduce
  consume := by
    intro p n
    rw [stack_shape]
    cases c with
    | inputs => exact ListConsumer.consume_le default _ _ _ 4 n
    | outputs => exact ListConsumer.consume_le default _ _ _ 8 n
    | certificates => exact ListConsumer.consume_le default _ _ _ 3 n
    | proposals => exact ListConsumer.consume_positive default _ _ n

def cost (c : Case) (p : Parameters) : Nat :=
  prefixCost c + 37 * (elements c p).length + 16 + postCost c

theorem execution (c : Case) (p : Parameters) (fuel : Nat) :
    cekExecuteProgram (script c).script (args p) fuel =
      if fuel ≤ cost c p then .BudgetExhausted
      else if test c (elements c p).length then .Halt (.VCon .Unit) else .Error := by
  have h := (certificate c).run_eq p fuel
  cases c <;> simpa only [certificate, start, cost, script, cekExecuteProgram,
    cekExecuteProgramWithSemanticVariant, ListConsumer.Certificate.cost] using h

theorem accepts_iff (c : Case) (p : Parameters) (fuel : Nat) :
    cekExecuteProgram (script c).script (args p) fuel = .Halt (.VCon .Unit) ↔
      test c (elements c p).length = true ∧ cost c p < fuel := by
  rw [execution]
  by_cases hf : fuel ≤ cost c p <;>
    cases ht : test c (elements c p).length <;> simp [hf] <;> omega

theorem eventually_accepts_iff (c : Case) (p : Parameters) :
    (∃ fuel, cekExecuteProgram (script c).script (args p) fuel = .Halt (.VCon .Unit)) ↔
      test c (elements c p).length = true := by
  constructor
  · rintro ⟨fuel, h⟩; exact ((accepts_iff c p fuel).mp h).1
  · intro h; exact ⟨cost c p + 1, (accepts_iff c p _).mpr ⟨h, by omega⟩⟩

end ContextCorpus.CountProperties
