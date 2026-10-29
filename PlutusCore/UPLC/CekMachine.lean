import PlutusCore.Default
import PlutusCore.UPLC.Builtins
import PlutusCore.UPLC.BuiltinFunctions.Evaluate
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.ExBudget
import PlutusCore.UPLC.CostModels
import PlutusCore.UPLC.PlutusScript

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.BuiltinFunctions.Evaluate
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.ExBudget
open PlutusCore.UPLC.CostModels
open PlutusCore.UPLC.PlutusScript (PlutusScript)

set_option linter.unusedVariables false
-- setting this option to avoid warning on marco rules format and unused variables

-- Define Frame
inductive Frame where
  | ForceFrame              : Frame
  | LeftApplicationToTerm   : Term → Environment → Frame
  | LeftApplicationToValue  : CekValue → Frame
  | RightApplicationOfValue : CekValue → Frame
  | ConstructorArgument     : Nat → List CekValue → List Term → Environment → Frame
  | CaseScrutinee           : List Term → Environment → Frame
deriving Repr

-- Define Stack
abbrev Stack := List Frame

-- Define State
inductive State where
  | Eval    : Stack → Environment → Term → State
  | Return  : Stack → CekValue → State
  | Error   : State
  | Halt    : CekValue → State
deriving Repr

-- Result type for budget aware execution
inductive EvaluationResult where
    | Success          : CekValue → ExBudget → EvaluationResult
    | BudgetExhausted  : ExBudget → EvaluationResult
    | EvaluationError  : EvaluationResult
    | StepLimitReached : ExBudget → EvaluationResult
deriving Repr


def evalBuiltin (semanticsVariant : BuiltinSemanticsVariant) (s : Stack) (b : BuiltinFun) (Vs : List CekValue) : State :=
  match evaluateBuiltinFunction semanticsVariant b Vs with
  | some V => State.Return s V
  | none => State.Error

open UPLC.Builtins
open ExpectedBuiltinArgs
open BuiltinNotations

def step (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) : State :=
  match Sigma with
  | State.Eval s ρ Tr =>
      match Tr with
      | Term.Var i =>
           match List.get?Internal ρ i with
           | some V => State.Return s V
           | none => State.Error
      | Term.Term.Const c => State.Return s (CekValue.VCon c)
      | Term.Lam M => State.Return s (CekValue.VLam M ρ)
      | Term.Delay M => State.Return s (CekValue.VDelay M ρ)
      | Term.Force M => State.Eval (Frame.ForceFrame :: s) ρ M
      | Term.Apply M N => State.Eval (Frame.LeftApplicationToTerm N ρ :: s) ρ M
      | Term.Constr i Ts =>
           match Ts with
           | M :: Ms => State.Eval (Frame.ConstructorArgument i [] Ms ρ :: s) ρ M
           | [] => State.Return s (CekValue.VConstr i [])
      | Term.Case N Ms => State.Eval (Frame.CaseScrutinee Ms ρ :: s) ρ N
      | Term.Builtin b => State.Return s (CekValue.VBuiltin b [] (α(b)))
      | Term.Error => State.Error

  | State.Return [] Vr => State.Halt Vr
  | State.Return (x :: s) Vr =>
         match x with
         | Frame.LeftApplicationToTerm M ρ =>
                State.Eval (Frame.RightApplicationOfValue Vr :: s) ρ M

         | Frame.LeftApplicationToValue V =>
             match Vr with
             | CekValue.VLam M ρ =>
                  State.Eval s (V :: ρ) M
             | CekValue.VBuiltin b Vs (ExpectedBuiltinArg.ArgV ⊙ η) =>
                  State.Return s (CekValue.VBuiltin b (V :: Vs) η)
             | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgV]) =>
                  evalBuiltin semanticsVariant s b (V :: Vs) -- considering args reversal when calling builtin
             | _ => State.Error

         | Frame.RightApplicationOfValue Va =>
             match Va with
             | CekValue.VLam M ρ =>
                   State.Eval s (Vr :: ρ) M
             | CekValue.VBuiltin b Vs (ExpectedBuiltinArg.ArgV ⊙ η) =>
                   State.Return s (CekValue.VBuiltin b (Vr :: Vs) η)
             | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgV]) =>
                   evalBuiltin semanticsVariant s b (Vr :: Vs) -- considering args reversal when calling builtin
             | _ => State.Error

         | Frame.ForceFrame =>
             match Vr with
             | CekValue.VDelay M ρ =>
                   State.Eval s ρ M
             | CekValue.VBuiltin b Vs (ExpectedBuiltinArg.ArgQ ⊙ η) =>
                   State.Return s (CekValue.VBuiltin b Vs η)
             | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgQ]) =>
                   evalBuiltin semanticsVariant s b Vs
             | _ => State.Error

         | Frame.ConstructorArgument i Vs Ts ρ =>
             match Ts with
             | M :: Ms => State.Eval (Frame.ConstructorArgument i (Vr :: Vs) Ms ρ :: s) ρ M
             | [] => State.Return s (CekValue.VConstr i (List.reverse (Vr :: Vs)))

         | Frame.CaseScrutinee Ms ρ =>
             match Vr with
             | CekValue.VConstr i Vs =>
                  match List.get?Internal Ms i with
                  | some mi => State.Eval (folding Vs s) ρ mi
                  | none => State.Error

             | CekValue.VCon (Const.Integer n) =>
                  if 0 ≤ n && n.toNat < Ms.length then
                    match Ms[n.toNat]? with
                    | some mi => State.Eval s ρ mi
                    | none => State.Error
                  else State.Error

             | CekValue.VCon (Const.Bool false) =>
                  if Ms.length == 1 || Ms.length == 2 then
                    match List.get?Internal Ms 0 with
                    | some mi => State.Eval s ρ mi
                    | none => State.Error
                  else State.Error

             | CekValue.VCon (Const.Bool true) =>
                  if Ms.length == 2 then
                    match List.get?Internal Ms 1 with
                    | some mi => State.Eval s ρ mi
                    | none => State.Error
                  else State.Error

             | CekValue.VCon Const.Unit =>
                   if Ms.length == 1 then
                     match Ms[0]? with
                     | some mi => State.Eval s ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.Pair p) =>
                   if Ms.length == 1 then
                     let Vs := [CekValue.VCon p.1, CekValue.VCon p.2]
                     match List.get?Internal Ms 0 with
                     | some mi => State.Eval (folding Vs s) ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.PairData p) =>
                   if Ms.length == 1 then
                     let Vs := [CekValue.VCon (Const.Data p.1), CekValue.VCon (Const.Data p.2)]
                     match List.get?Internal Ms 0 with
                     | some mi => State.Eval (folding Vs s) ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.ConstList (c :: cs)) =>
                   if Ms.length == 1 || Ms.length == 2 then
                     let Vs := [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)]
                     match List.get?Internal Ms 0 with
                     | some mi => State.Eval (folding Vs s) ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.ConstList []) =>
                   if Ms.length == 2 then
                     match List.get?Internal Ms 1 with
                     | some mi => State.Eval s ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.ConstDataList (c :: cs)) =>
                   if Ms.length == 1 || Ms.length == 2 then
                     let Vs := [CekValue.VCon (.Data c), CekValue.VCon (Const.ConstDataList cs)]
                     match Ms[0]? with
                     | some mi => State.Eval (folding Vs s) ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.ConstDataList []) =>
                   if Ms.length == 2 then
                     match List.get?Internal Ms 1 with
                     | some mi => State.Eval s ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.ConstPairDataList (c :: cs)) =>
                   if Ms.length == 1 || Ms.length == 2 then
                     let Vs := [CekValue.VCon (.PairData c), CekValue.VCon (Const.ConstPairDataList cs)]
                     match List.get?Internal Ms 0 with
                     | some mi => State.Eval (folding Vs s) ρ mi
                     | none => State.Error
                   else State.Error

             | CekValue.VCon (Const.ConstPairDataList []) =>
                   if Ms.length == 2 then
                     match List.get?Internal Ms 1 with
                     | some mi => State.Eval s ρ mi
                     | none => State.Error
                   else State.Error

             | _ => State.Error

  | State.Halt V => State.Halt V
  | State.Error => State.Error

  where
    folding (xs : List CekValue) (init : Stack) : Stack :=
      match xs with
      | [] => init
      | x :: xs' => Frame.LeftApplicationToValue x :: (folding xs' init)

-- Define Run Steps
def runSteps (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) (n : Nat) : State :=
  match n, Sigma with
  | _, State.Halt V => Sigma
  | _, State.Error => Sigma
  | 0, _ => State.Error -- change to error when num steps exhausted
  | Nat.succ n, _ => runSteps semanticsVariant (step semanticsVariant Sigma) n

-- Define Apply Params
def applyParams (body : Term) (params : List Term) : Term :=
  match params with
  | h :: t => applyParams (Term.Apply body h) t
  | [] => body

-- Define Initial State
def initialState (t : Term) : State :=
  State.Eval [] [] t

def cekExecuteProgramWithSemanticVariant (semanticVariant : BuiltinSemanticsVariant) (p : Program) (params : List Term) (n : Nat) : State :=
  match p with
  | Program.Program _ body =>
      runSteps semanticVariant (initialState (applyParams body params)) n

-- Define CEK Execution
def cekExecuteProgram : Program → List Term →  Nat → State := cekExecuteProgramWithSemanticVariant default


/-! ## Execution cost

Costing is opt-in: `runSteps` above does no bookkeeping, and `runStepsWithCost` runs the same
steps while adding up what they cost.  -/

-- Calculate the cost of a single CEK machine step based on the current state
def calculateStepCostr (costs : CekMachineCosts) (Sigma : State) : ExBudget :=
  match Sigma with
    | .Eval   _ _ (.Var _)      => costs.stepCostVar
    | .Eval   _ _ (.Const _)    => costs.stepCostConst
    | .Eval   _ _ (.Lam _)      => costs.stepCostLam
    | .Eval   _ _ (.Delay _)    => costs.stepCostDelay
    | .Eval   _ _ (.Force _)    => costs.stepCostForce
    | .Eval   _ _ (.Apply _ _)  => costs.stepCostApply
    | .Eval   _ _ (.Builtin _)  => costs.stepCostBuiltin
    | .Eval   _ _ (.Constr _ _) => costs.stepCostConstr
    | .Eval   _ _ (.Case _ _)   => costs.stepCostCase
    | .Eval   _ _  .Error       => .zero
    | .Return _ _               => .zero
    | .Halt   _                 => .zero
    | .Error                    => .zero

/-- The builtin application that stepping from `Sigma` evaluates, if any: the builtin and its
    arguments, last-applied first, as `evalBuiltin` receives them (and as the cost-model formulas
    in CostModels.lean assume). These are exactly the cases where `step` calls `evalBuiltin`. -/
def saturatedBuiltin? (Sigma : State) : Option (BuiltinFun × List CekValue) :=
  match Sigma with
  | State.Return (x :: _) Vr =>
      match x with
      | Frame.LeftApplicationToValue V =>
          match Vr with
          | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgV]) => some (b, V :: Vs)
          | _ => none
      | Frame.RightApplicationOfValue Va =>
          match Va with
          | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgV]) => some (b, Vr :: Vs)
          | _ => none
      | Frame.ForceFrame =>
          match Vr with
          | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgQ]) => some (b, Vs)
          | _ => none
      | _ => none
  | _ => none

def getBuiltinCostIfExecuted (semVar : BuiltinSemanticsVariant) (Sigma : State) : ExBudget :=
  match saturatedBuiltin? Sigma with
  | some (b, args) => builtinCostSelected semVar b args
  | none           => .zero

-- Map semantics variant to the corresponding CEK machine step costs.
-- See: https://github.com/IntersectMBO/plutus/blob/master/plutus-ledger-api/src/PlutusLedgerApi/MachineParameters.hs
--   PlutusV1/V2, pre-Conway   → VariantA (defaultCekMachineCostsA)
--   PlutusV1/V2, post-Conway  → VariantD (defaultCekMachineCostsD, same step costs as C)
--   PlutusV3,    pre-Conway   → VariantC (defaultCekMachineCostsC)
--   PlutusV3,    post-Conway  → VariantE (defaultCekMachineCostsE, same step costs as C)
def semVarToCosts : BuiltinSemanticsVariant → CekMachineCosts
  | .defaultFunSemanticsVariantA => defaultCekMachineCostsA
  | .defaultFunSemanticsVariantB => defaultCekMachineCostsB
  | .defaultFunSemanticsVariantC => defaultCekMachineCostsC
  | .defaultFunSemanticsVariantD => defaultCekMachineCostsD
  | .defaultFunSemanticsVariantE => defaultCekMachineCostsE

/-- What a list of builtin calls costs. -/
def builtinCallsCost (semanticsVariant : BuiltinSemanticsVariant) : List (BuiltinFun × List CekValue) → ExBudget
  | []                 => .zero
  | (b, args) :: calls => builtinCostSelected semanticsVariant b args + builtinCallsCost semanticsVariant calls

def builtinCallsCostTR (semanticsVariant : BuiltinSemanticsVariant) (xs : List (BuiltinFun × List CekValue)) : ExBudget :=
  let rec loop (acc : ExBudget) : List (BuiltinFun × List CekValue) → ExBudget
    | []                 => acc
    | (b, args) :: calls => loop (acc + builtinCostSelected semanticsVariant b args) calls
  loop .zero xs

theorem builtinCallsCostTR.loop_TR_correct : ∀ s exBudget xs, loop s exBudget xs = exBudget + loop s ExBudget.zero xs := by
  intros s exBudget xs
  induction xs generalizing exBudget with
  | nil          => simp [loop]
  | cons x xs ih =>
      simp [loop]
      rw [ih, ih (builtinCostSelected s x.fst x.snd)]
      simp [ExBudget.add_assoc]

@[csimp]
theorem builtinCallsCost_equiv_TR : builtinCallsCost = builtinCallsCostTR := by
  funext s xs
  induction xs with
  | nil          => simp [builtinCallsCost, builtinCallsCostTR, builtinCallsCostTR.loop]
  | cons x xs ih =>
      simp [builtinCallsCost, builtinCallsCostTR, builtinCallsCostTR.loop] at *
      rw [ih, ←builtinCallsCostTR.loop_TR_correct]

/-- The steps of `runSteps`, adding the step costs to `stepCost` and recording the builtin calls
    in `calls`, most recent first. It stops at `Halt`, at `Error`, or when the steps run out, and
    returns the state reached. -/
def runStepsCosting (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) (n : Nat)
    (stepCost : ExBudget) (calls : List (BuiltinFun × List CekValue)) : State × ExBudget × List (BuiltinFun × List CekValue) :=
  match n, Sigma with
  | _, State.Halt V => (State.Halt V, stepCost, calls)
  | _, State.Error  => (State.Error, stepCost, calls)
  | 0, _            => (Sigma, stepCost, calls)
  | .succ n, _ =>
      runStepsCosting semanticsVariant (step semanticsVariant Sigma) n
        (stepCost + calculateStepCostr (semVarToCosts semanticsVariant) Sigma)
        (match saturatedBuiltin? Sigma with
         | some call => call :: calls
         | none => calls)

/-- `runSteps` with costs: the state reached in at most `n` steps (`Halt`, `Error`, or where the
    steps ran out, which `runSteps` turns into `Error`) and what the steps taken cost. -/
def runStepsWithCost (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) (n : Nat) : State × ExBudget :=
  let r := runStepsCosting semanticsVariant Sigma n ExBudget.zero []
  (r.1, r.2.1 + builtinCallsCost semanticsVariant r.2.2)

/-- Native costing loop. Charge each builtin before executing it, rather than
    retaining its arguments in a call history until evaluation has finished.
    The machine costs are selected once by the caller. -/
def runStepsCostingEager (sv : BuiltinSemanticsVariant) (costs : CekMachineCosts)
    (Sigma : State) (n : Nat) (cost : ExBudget) : State × ExBudget :=
  match n, Sigma with
  | _, State.Halt V => (State.Halt V, cost)
  | _, State.Error => (State.Error, cost)
  | 0, _ => (Sigma, cost)
  | .succ n, _ =>
      let cost := cost + calculateStepCostr costs Sigma
      let cost := match saturatedBuiltin? Sigma with
        | some (b, args) => cost + builtinCostSelected sv b args
        | none => cost
      runStepsCostingEager sv costs (step sv Sigma) n cost

/-- Eager charging preserves both the complete final state and the exact cost,
    including failed builtin applications and runs stopped by the fuel limit. -/
theorem runStepsCostingEager_eq (sv : BuiltinSemanticsVariant) (Sigma : State) (n : Nat)
    (stepCost : ExBudget) (calls : List (BuiltinFun × List CekValue)) :
    runStepsCostingEager sv (semVarToCosts sv) Sigma n (stepCost + builtinCallsCost sv calls) =
      let r := runStepsCosting sv Sigma n stepCost calls
      (r.1, r.2.1 + builtinCallsCost sv r.2.2) := by
  induction n generalizing Sigma stepCost calls with
  | zero => cases Sigma <;> simp [runStepsCostingEager, runStepsCosting]
  | succ n ih =>
      cases Sigma with
      | Halt V => simp [runStepsCostingEager, runStepsCosting]
      | Error => simp [runStepsCostingEager, runStepsCosting]
      | Eval st rho t =>
          simp only [runStepsCostingEager, runStepsCosting]
          rw [← ih]
          congr 1
          cases h : saturatedBuiltin? (State.Eval st rho t) with
          | none =>
              apply ExBudget.ext <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          | some call =>
              rcases call with ⟨b, args⟩
              simp only [builtinCallsCost]
              apply ExBudget.ext <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      | Return st v =>
          simp only [runStepsCostingEager, runStepsCosting]
          rw [← ih]
          congr 1
          cases h : saturatedBuiltin? (State.Return st v) with
          | none =>
              apply ExBudget.ext <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          | some call =>
              rcases call with ⟨b, args⟩
              simp only [builtinCallsCost]
              apply ExBudget.ext <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-! ### Fused compiled evaluator

The continuations below let the compiler dispatch directly to the next loop iteration.
Only stopping constructs a State; ordinary transitions pass its fields as loop arguments.
The logical evaluator and its proof interface are retained above.
-/
namespace Runtime

@[inline] def budget (cpu mem : Nat) : ExBudget := ⟨⟨cpu⟩, ⟨mem⟩⟩

@[simp] theorem budget_add (cpu mem : Nat) (cost : ExBudget) :
    budget cpu mem + cost = budget (cpu + cost.exBudgetCPU.unExCPU)
      (mem + cost.exBudgetMemory.unExMemory) := rfl

@[inline] def termCost (costs : CekMachineCosts) (t : Term) : ExBudget :=
  match t with
  | .Var _ => costs.stepCostVar
  | .Const _ => costs.stepCostConst
  | .Lam _ => costs.stepCostLam
  | .Delay _ => costs.stepCostDelay
  | .Force _ => costs.stepCostForce
  | .Apply _ _ => costs.stepCostApply
  | .Builtin _ => costs.stepCostBuiltin
  | .Constr _ _ => costs.stepCostConstr
  | .Case _ _ => costs.stepCostCase
  | .Error => .zero

@[inline] def dispatchEval {α : Type}
    (onEval : Stack → Environment → Term → α)
    (onReturn : Stack → CekValue → α) (onError : Unit → α)
    (s : Stack) (ρ : Environment) (Tr : Term) : α :=
  match Tr with
  | Term.Var i =>
       match List.get?Internal ρ i with
       | some V => onReturn s V
       | none => onError ()
  | Term.Term.Const c => onReturn s (CekValue.VCon c)
  | Term.Lam M => onReturn s (CekValue.VLam M ρ)
  | Term.Delay M => onReturn s (CekValue.VDelay M ρ)
  | Term.Force M => onEval (Frame.ForceFrame :: s) ρ M
  | Term.Apply M N => onEval (Frame.LeftApplicationToTerm N ρ :: s) ρ M
  | Term.Constr i Ts =>
       match Ts with
       | M :: Ms => onEval (Frame.ConstructorArgument i [] Ms ρ :: s) ρ M
       | [] => onReturn s (CekValue.VConstr i [])
  | Term.Case N Ms => onEval (Frame.CaseScrutinee Ms ρ :: s) ρ N
  | Term.Builtin b => onReturn s (CekValue.VBuiltin b [] (α(b)))
  | Term.Error => onError ()

@[inline] def dispatchReturn {α : Type}
    (onEval : Stack → Environment → Term → α)
    (onReturn : Stack → CekValue → α) (onError : Unit → α)
    (onHalt : CekValue → α) (onBuiltin : Stack → BuiltinFun → List CekValue → α)
    (stack : Stack) (Vr : CekValue) : α :=
  match stack with
  | [] => onHalt Vr
  | x :: s =>
    match x with
    | Frame.LeftApplicationToTerm M ρ =>
           onEval (Frame.RightApplicationOfValue Vr :: s) ρ M

    | Frame.LeftApplicationToValue V =>
        match Vr with
        | CekValue.VLam M ρ =>
             onEval s (V :: ρ) M
        | CekValue.VBuiltin b Vs (ExpectedBuiltinArg.ArgV ⊙ η) =>
             onReturn s (CekValue.VBuiltin b (V :: Vs) η)
        | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgV]) =>
             onBuiltin s b (V :: Vs) -- considering args reversal when calling builtin
        | _ => onError ()

    | Frame.RightApplicationOfValue Va =>
        match Va with
        | CekValue.VLam M ρ =>
              onEval s (Vr :: ρ) M
        | CekValue.VBuiltin b Vs (ExpectedBuiltinArg.ArgV ⊙ η) =>
              onReturn s (CekValue.VBuiltin b (Vr :: Vs) η)
        | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgV]) =>
              onBuiltin s b (Vr :: Vs) -- considering args reversal when calling builtin
        | _ => onError ()

    | Frame.ForceFrame =>
        match Vr with
        | CekValue.VDelay M ρ =>
              onEval s ρ M
        | CekValue.VBuiltin b Vs (ExpectedBuiltinArg.ArgQ ⊙ η) =>
              onReturn s (CekValue.VBuiltin b Vs η)
        | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgQ]) =>
              onBuiltin s b Vs
        | _ => onError ()

    | Frame.ConstructorArgument i Vs Ts ρ =>
        match Ts with
        | M :: Ms => onEval (Frame.ConstructorArgument i (Vr :: Vs) Ms ρ :: s) ρ M
        | [] => onReturn s (CekValue.VConstr i (List.reverse (Vr :: Vs)))

    | Frame.CaseScrutinee Ms ρ =>
        match Vr with
        | CekValue.VConstr i Vs =>
             match List.get?Internal Ms i with
             | some mi => onEval (step.folding Vs s) ρ mi
             | none => onError ()

        | CekValue.VCon (Const.Integer n) =>
             if 0 ≤ n && n.toNat < Ms.length then
               match Ms[n.toNat]? with
               | some mi => onEval s ρ mi
               | none => onError ()
             else onError ()

        | CekValue.VCon (Const.Bool false) =>
             if Ms.length == 1 || Ms.length == 2 then
               match List.get?Internal Ms 0 with
               | some mi => onEval s ρ mi
               | none => onError ()
             else onError ()

        | CekValue.VCon (Const.Bool true) =>
             if Ms.length == 2 then
               match List.get?Internal Ms 1 with
               | some mi => onEval s ρ mi
               | none => onError ()
             else onError ()

        | CekValue.VCon Const.Unit =>
              if Ms.length == 1 then
                match Ms[0]? with
                | some mi => onEval s ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.Pair p) =>
              if Ms.length == 1 then
                let Vs := [CekValue.VCon p.1, CekValue.VCon p.2]
                match List.get?Internal Ms 0 with
                | some mi => onEval (step.folding Vs s) ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.PairData p) =>
              if Ms.length == 1 then
                let Vs := [CekValue.VCon (Const.Data p.1), CekValue.VCon (Const.Data p.2)]
                match List.get?Internal Ms 0 with
                | some mi => onEval (step.folding Vs s) ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.ConstList (c :: cs)) =>
              if Ms.length == 1 || Ms.length == 2 then
                let Vs := [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)]
                match List.get?Internal Ms 0 with
                | some mi => onEval (step.folding Vs s) ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.ConstList []) =>
              if Ms.length == 2 then
                match List.get?Internal Ms 1 with
                | some mi => onEval s ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.ConstDataList (c :: cs)) =>
              if Ms.length == 1 || Ms.length == 2 then
                let Vs := [CekValue.VCon (.Data c), CekValue.VCon (Const.ConstDataList cs)]
                match Ms[0]? with
                | some mi => onEval (step.folding Vs s) ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.ConstDataList []) =>
              if Ms.length == 2 then
                match List.get?Internal Ms 1 with
                | some mi => onEval s ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.ConstPairDataList (c :: cs)) =>
              if Ms.length == 1 || Ms.length == 2 then
                let Vs := [CekValue.VCon (.PairData c), CekValue.VCon (Const.ConstPairDataList cs)]
                match List.get?Internal Ms 0 with
                | some mi => onEval (step.folding Vs s) ρ mi
                | none => onError ()
              else onError ()

        | CekValue.VCon (Const.ConstPairDataList []) =>
              if Ms.length == 2 then
                match List.get?Internal Ms 1 with
                | some mi => onEval s ρ mi
                | none => onError ()
              else onError ()

        | _ => onError ()

private def unusedValue : CekValue := .VCon .Unit

/-- One tail-recursive loop with scalar state fields. The unused environment/term/value
    slots contain shared constants; no State or ExBudget is allocated per transition. -/
def run (sv : BuiltinSemanticsVariant) (costs : CekMachineCosts) (fuel : Nat)
    (returning : Bool) (s : Stack) (ρ : Environment) (t : Term) (v : CekValue)
    (cpu mem : Nat) : State × ExBudget :=
  match fuel with
  | 0 => (if returning then .Return s v else .Eval s ρ t, budget cpu mem)
  | fuel + 1 =>
    if returning then
      dispatchReturn
        (fun s ρ t => run sv costs fuel false s ρ t unusedValue cpu mem)
        (fun s v => run sv costs fuel true s [] .Error v cpu mem)
        (fun _ => (.Error, budget cpu mem))
        (fun v => (.Halt v, budget cpu mem))
        (fun s b args =>
          let charge := builtinCostSelected sv b args
          let cpu := cpu + charge.exBudgetCPU.unExCPU
          let mem := mem + charge.exBudgetMemory.unExMemory
          match evaluateBuiltinFunction sv b args with
          | some v => run sv costs fuel true s [] .Error v cpu mem
          | none => (.Error, budget cpu mem))
        s v
    else
      let charge := termCost costs t
      let cpu := cpu + charge.exBudgetCPU.unExCPU
      let mem := mem + charge.exBudgetMemory.unExMemory
      dispatchEval
        (fun s ρ t => run sv costs fuel false s ρ t unusedValue cpu mem)
        (fun s v => run sv costs fuel true s [] .Error v cpu mem)
        (fun _ => (.Error, budget cpu mem)) s ρ t

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem run_eq (sv : BuiltinSemanticsVariant) (costs : CekMachineCosts) (fuel : Nat)
    (returning : Bool) (s : Stack) (ρ : Environment) (t : Term) (v : CekValue)
    (cpu mem : Nat) :
    run sv costs fuel returning s ρ t v cpu mem =
      runStepsCostingEager sv costs (if returning then .Return s v else .Eval s ρ t)
        fuel (budget cpu mem) := by
  induction fuel generalizing returning s ρ t v cpu mem with
  | zero => cases returning <;> rfl
  | succ fuel ih =>
      cases returning with
      | false =>
          cases t <;>
            simp [run, dispatchEval, termCost, step, saturatedBuiltin?,
              runStepsCostingEager, ih]
          all_goals repeat' (first | rfl | (split <;> try simp_all [runStepsCostingEager]))
      | true =>
          cases s with
          | nil => simp [run, dispatchReturn, runStepsCostingEager, step, saturatedBuiltin?,
              calculateStepCostr]
          | cons f s =>
              cases f <;>
                simp [run, dispatchReturn, runStepsCostingEager, step, saturatedBuiltin?,
                  calculateStepCostr, evalBuiltin, ih]
              all_goals repeat' (first | rfl | (split <;> try simp_all [runStepsCostingEager]))

def fromState (sv : BuiltinSemanticsVariant) (costs : CekMachineCosts) (state : State)
    (fuel : Nat) (cost : ExBudget) : State × ExBudget :=
  match state with
  | .Eval s ρ t => run sv costs fuel false s ρ t unusedValue
      cost.exBudgetCPU.unExCPU cost.exBudgetMemory.unExMemory
  | .Return s v => run sv costs fuel true s [] .Error v
      cost.exBudgetCPU.unExCPU cost.exBudgetMemory.unExMemory
  | .Error => (.Error, cost)
  | .Halt v => (.Halt v, cost)

end Runtime

@[csimp]
theorem runStepsCostingEager_eq_runtime : runStepsCostingEager = Runtime.fromState := by
  funext sv costs state fuel cost
  cases state <;> simp [Runtime.fromState, Runtime.run_eq, Runtime.budget, runStepsCostingEager]

/-- Compiled entry point; the logical evaluator retains its call-history model. -/
def runStepsWithCostEager (sv : BuiltinSemanticsVariant) (Sigma : State) (n : Nat) : State × ExBudget :=
  runStepsCostingEager sv (semVarToCosts sv) Sigma n ExBudget.zero

@[csimp]
theorem runStepsWithCost_eq_eager : runStepsWithCost = runStepsWithCostEager := by
  funext sv Sigma n
  simpa [runStepsWithCost, runStepsWithCostEager, builtinCallsCost] using
    (runStepsCostingEager_eq sv Sigma n ExBudget.zero []).symm

/-- The state a program reaches in at most `n` steps and what it cost, startup cost included. -/
def cekExecuteProgramWithCost (semanticVariant : BuiltinSemanticsVariant) (p : Program) (params : List Term) (n : Nat) : State × ExBudget :=
  match p with
  | Program.Program _ body =>
      let r := runStepsWithCost semanticVariant (initialState (applyParams body params)) n
      (r.1, (semVarToCosts semanticVariant).startupCost + r.2)

/-- Judge a costed run against a budget.

    The Plutus reference (restricting mode) checks the budget at each charge and fails at the
    first it cannot afford. Costs are never negative, so no part of a run costs more than all of
    it: when the run ends in `Halt` or `Error`, comparing its total cost against the budget gives
    the same outcome, and on success the same budget consumed. A run that hit the step limit is
    out of budget if it already cost too much, and inconclusive otherwise. -/
def EvaluationResult.ofCostedRun (budget : ExBudget) : State × ExBudget → EvaluationResult
  | (Sigma, cost) =>
      if budget.canAfford cost
        then
          match Sigma with
          | State.Halt V => EvaluationResult.Success V cost
          | State.Error => EvaluationResult.EvaluationError
          | _ => EvaluationResult.StepLimitReached cost
        else
          EvaluationResult.BudgetExhausted (budget - cost)

def cekExecuteProgramWithBudget (p : Program) (plutusVer : PlutusVersion) (protocolVer : ProtocolVersion)
    (params : List Term) (budget : ExBudget) (maxSteps : Nat) : EvaluationResult :=
  EvaluationResult.ofCostedRun budget
    (cekExecuteProgramWithCost (PlutusVersion.toSemanticsVariant plutusVer protocolVer)
      p params maxSteps)

/-- `cekExecuteProgramWithCost` under the semantics and cost model of the script's ledger language,
    post-Conway. -/
def cekExecuteScriptWithCost (ps : PlutusScript) (params : List Term) (n : Nat) : State × ExBudget :=
  cekExecuteProgramWithCost (PlutusVersion.toSemanticsVariant ps.lang.toPlutusVersion .postConway)
    ps.script params n

/-- The budget a run consumed, if it succeeded. -/
def consumed? : EvaluationResult → Option ExBudget
  | .Success _ b => some b
  | _            => none

def isEvaluationError : EvaluationResult → Bool
  | .EvaluationError => true
  | _                => false

end PlutusCore.UPLC.CekMachine
