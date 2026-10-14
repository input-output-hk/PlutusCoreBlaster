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
def builtinCallsCost (semanticsVariant : BuiltinSemanticsVariant) :
    List (BuiltinFun × List CekValue) → ExBudget
  | [] => ExBudget.zero
  | (b, args) :: calls => builtinCostSelected semanticsVariant b args + builtinCallsCost semanticsVariant calls

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

end PlutusCore.UPLC.CekMachine
