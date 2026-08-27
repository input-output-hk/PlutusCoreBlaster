import PlutusCore.Default
import PlutusCore.UPLC.Builtins
import PlutusCore.UPLC.BuiltinFunctions.Evaluate
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.ExBudget
import PlutusCore.UPLC.CostModels

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.Integer (Integer)
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.BuiltinFunctions.Evaluate
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.ExBudget
open PlutusCore.UPLC.CostModels

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
    | Success : CekValue → ExBudget → EvaluationResult
    | BudgetExhausted : ExBudget → EvaluationResult
    | EvaluationError : EvaluationResult
deriving Repr


def evalBuiltin (semanticsVariant : BuiltinSemanticsVariant) (s : Stack) (b : BuiltinFun) (Vs : List CekValue) : State :=
  match evaluateBuiltinFunction semanticsVariant b Vs with
  | some V => State.Return s V
  | none => State.Error

open UPLC.Builtins
open ExpectedBuiltinArgs
open BuiltinNotations

/-- Branch selection for `case` on an integer scrutinee: the `i`-th branch of
    `Ms` when `0 ≤ i < Ms.length`, and `none` otherwise, so that a negative or
    out-of-range tag is a machine error as in the Plutus reference implementation.

    This is `if 0 ≤ i then Ms[i.toNat]? else none` (see
    `PlutusCore.UPLC.CekMachine.caseBranch_eq_getElem?`), written as a fold over
    the branch list so that the tag never appears as a `match` discriminant:
    `Ms[i.toNat]?` cannot be reduced by the SMT backend when `i` is symbolic,
    whereas this definition unfolds, for a literal branch list, to a plain chain
    of integer comparisons. -/
def caseBranch (Ms : List Term) (i : Integer) : Option Term :=
  Ms.foldr (fun M rest i => if i = 0 then some M else rest (i - 1)) (fun _ => none) i

def step (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) : State :=
  match Sigma with
  | State.Eval s ρ Tr =>
      match Tr with
      | Term.Var i =>
           match List.get?Internal ρ i with
           | some V => State.Return s V
           | none => State.Error
      | Term.Term.Const c => State.Return s (CekValue.VCon c)
      | Term.Lam x M => State.Return s (CekValue.VLam x M ρ)
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
             | CekValue.VLam _ M ρ =>
                  State.Eval s (V :: ρ) M
             | CekValue.VBuiltin b Vs (ExpectedBuiltinArg.ArgV ⊙ η) =>
                  State.Return s (CekValue.VBuiltin b (V :: Vs) η)
             | CekValue.VBuiltin b Vs (a[ExpectedBuiltinArg.ArgV]) =>
                  evalBuiltin semanticsVariant s b (V :: Vs) -- considering args reversal when calling builtin
             | _ => State.Error

         | Frame.RightApplicationOfValue Va =>
             match Va with
             | CekValue.VLam _ M ρ =>
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

         -- NOTE: every alternative below matches at most down to the `Const`
         -- constructor and binds its payload; any further case analysis on that
         -- payload is done in the body of the alternative.  This keeps the whole
         -- `match` reducible as soon as `Vr` is a known `CekValue`/`Const`
         -- constructor, even when the payload is symbolic, which is what the SMT
         -- backend needs in order to see through a `case`.
         | Frame.CaseScrutinee Ms ρ =>
             match Vr with
             | CekValue.VConstr i Vs =>
                  match List.get?Internal Ms i with
                  | some mi => State.Eval (folding Vs s) ρ mi
                  | none => State.Error

             | CekValue.VCon (Const.Integer n) =>
                  match caseBranch Ms n with
                  | some mi => State.Eval s ρ mi
                  | none => State.Error

             | CekValue.VCon (Const.Bool b) =>
                  if b then
                    if Ms.length == 2 then
                      match List.get?Internal Ms 1 with
                      | some mi => State.Eval s ρ mi
                      | none => State.Error
                    else State.Error
                  else
                    if Ms.length == 1 || Ms.length == 2 then
                      match List.get?Internal Ms 0 with
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

             | CekValue.VCon (Const.ConstList l) =>
                   match l with
                   | c :: cs =>
                     if Ms.length == 1 || Ms.length == 2 then
                       let Vs := [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)]
                       match List.get?Internal Ms 0 with
                       | some mi => State.Eval (folding Vs s) ρ mi
                       | none => State.Error
                     else State.Error
                   | [] =>
                     if Ms.length == 2 then
                       match List.get?Internal Ms 1 with
                       | some mi => State.Eval s ρ mi
                       | none => State.Error
                     else State.Error

             | CekValue.VCon (Const.ConstDataList l) =>
                   match l with
                   | c :: cs =>
                     if Ms.length == 1 || Ms.length == 2 then
                       let Vs := [CekValue.VCon (.Data c), CekValue.VCon (Const.ConstDataList cs)]
                       match Ms[0]? with
                       | some mi => State.Eval (folding Vs s) ρ mi
                       | none => State.Error
                     else State.Error
                   | [] =>
                     if Ms.length == 2 then
                       match List.get?Internal Ms 1 with
                       | some mi => State.Eval s ρ mi
                       | none => State.Error
                     else State.Error

             | CekValue.VCon (Const.ConstPairDataList l) =>
                   match l with
                   | c :: cs =>
                     if Ms.length == 1 || Ms.length == 2 then
                       let Vs := [CekValue.VCon (.PairData c), CekValue.VCon (Const.ConstPairDataList cs)]
                       match List.get?Internal Ms 0 with
                       | some mi => State.Eval (folding Vs s) ρ mi
                       | none => State.Error
                     else State.Error
                   | [] =>
                     if Ms.length == 2 then
                       match List.get?Internal Ms 1 with
                       | some mi => State.Eval s ρ mi
                       | none => State.Error
                     else State.Error

             | _ => State.Error

  | _ => State.Error

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


-- Budget aware CEK execution
-- Calculate the cost of a single CEK machine step based on the current state
def calculateStepCostr (costs : CekMachineCosts) (Sigma : State) : ExBudget :=
  match Sigma with
    | State.Eval _ _ (Term.Var _)           => costs.stepCostVar
    | State.Eval _ _ (Term.Term.Const _)    => costs.stepCostConst
    | State.Eval _ _ (Term.Lam _ _)         => costs.stepCostLam
    | State.Eval _ _ (Term.Delay _)         => costs.stepCostDelay
    | State.Eval _ _ (Term.Force _)         => costs.stepCostForce
    | State.Eval _ _ (Term.Apply _ _)       => costs.stepCostApply
    | State.Eval _ _ (Term.Builtin _)       => costs.stepCostBuiltin
    | State.Eval _ _ (Term.Constr _ _)      => costs.stepCostConstr
    | State.Eval _ _ (Term.Case _ _)        => costs.stepCostCase
    | State.Eval _ _ Term.Error             => ExBudget.zero
    | State.Return _ _                      => ExBudget.zero
    | State.Error                           => ExBudget.zero
    | State.Halt _                          => ExBudget.zero

def getBuiltinCostIfExecuted (semVar : BuiltinSemanticsVariant) (Sigma : State) : ExBudget :=
    match Sigma with
    -- Check Return states that will call evalBuiltin with final argument.
    -- Pass args in the same order evalBuiltin sees them (V :: Vs) — last-applied
    -- first, matching what the cost-model formulas in CostModels.lean assume.
    | State.Return (Frame.RightApplicationOfValue (CekValue.VBuiltin b Vs (a[_])) :: _) V =>
        builtinCostSelected semVar b (V :: Vs)
    | State.Return (Frame.LeftApplicationToValue V :: _) (CekValue.VBuiltin b Vs (a[_])) =>
        builtinCostSelected semVar b (V :: Vs)
    | State.Return (Frame.ForceFrame :: _) (CekValue.VBuiltin b Vs (a[_])) =>
        builtinCostSelected semVar b Vs
    | _ => ExBudget.zero

def stepWithBudget
    (semanticsVariant : BuiltinSemanticsVariant)
    (costs : CekMachineCosts)
    (Sigma : State)
    (budget : ExBudget) : Option (State × ExBudget) :=
    let stepCost := calculateStepCostr costs Sigma
    let builtinCost := getBuiltinCostIfExecuted semanticsVariant Sigma
    let totalCost := stepCost + builtinCost
    if budget.canAfford totalCost then
        some (step semanticsVariant Sigma, budget - totalCost)
    else
        none

def runStepsWithBudget
    (semanticsVariant : BuiltinSemanticsVariant)
    (costs : CekMachineCosts)
    (Sigma : State)
    (budget : ExBudget)
    (initialBudget : ExBudget) : EvaluationResult :=
    match Sigma with
    | State.Halt V  => EvaluationResult.Success V (initialBudget - budget)
    | State.Error   => EvaluationResult.EvaluationError
    | _ =>
        match stepWithBudget semanticsVariant costs Sigma budget with
        | none => EvaluationResult.BudgetExhausted budget
        | some (newState, newBudget) => runStepsWithBudget semanticsVariant costs newState newBudget initialBudget
    termination_by budget.exBudgetCPU.unExCPU + budget.exBudgetMemory.unExMemory
    decreasing_by
        sorry

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

def cekExecuteProgramWithBudget
    (p : Program)
    (plutusVer : PlutusVersion)
    (protocolVer : ProtocolVersion)
    (params : List Term)
    (budget : ExBudget) : EvaluationResult :=
    match p with
    | Program.Program _ body =>
        let semVar := PlutusVersion.toSemanticsVariant plutusVer protocolVer
        let costs  := semVarToCosts semVar
        -- Startup cost is charged once up front, matching the Plutus reference
        if budget.canAfford costs.startupCost then
            runStepsWithBudget semVar costs (initialState (applyParams body params))
                (budget - costs.startupCost) budget
        else
            EvaluationResult.BudgetExhausted budget

end PlutusCore.UPLC.CekMachine
