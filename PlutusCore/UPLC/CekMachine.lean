import PlutusCore.Default
import PlutusCore.UPLC.Builtins
import PlutusCore.UPLC.BuiltinFunctions.Evaluate
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.ExBudget
import PlutusCore.UPLC.CostModels

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
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

-- Define Helper Functions
-- Define ifBoundOtherwiseError
def ifBoundOtherwiseError (s : Stack) (p : Environment) (x : String) : State :=
  match p with
  | .EmptyEnvironment => State.Error
  | .NonEmptyEnvironment p' x' V =>
      if x = x' then State.Return s V else ifBoundOtherwiseError s p' x

-- Define ifArgVOtherwiseError
def ifArgVOtherwiseError (Sigma : State) (l : ExpectedBuiltinArg) : State :=
  match l with
  | ExpectedBuiltinArg.ArgV => Sigma
  | ExpectedBuiltinArg.ArgQ => State.Error

def ifArgQOtherwiseError (Sigma : State) (l : ExpectedBuiltinArg) : State :=
  match l with
  | ExpectedBuiltinArg.ArgQ => Sigma
  | ExpectedBuiltinArg.ArgV => State.Error

def evalBuiltinReference (semanticsVariant : BuiltinSemanticsVariant) (s : Stack) (b : BuiltinFun) (Vs : List CekValue) : State :=
  match evaluateBuiltinFunction semanticsVariant b Vs with
  | some V => State.Return s V
  | none => State.Error

/-!
The generic builtin path constructs `Except`, then `Option`, then dispatches
back to `State`.  For symbolic `Data` destructors this makes the same five-way
`Data` choice cross several generic matchers.  Consume the already-known list,
CEK-value and constant constructors one layer at a time and return the CEK
state directly.  This retains the exact builtin semantics while keeping the
symbolic choice at its actual `Data` leaf.
-/

private def evalUnConstrData (s : Stack) : List CekValue → State
  | [CekValue.VCon (Const.Data (.Constr idx fields))] =>
      State.Return s (.VCon (.Pair (.Integer idx, .ConstDataList fields)))
  | _ => State.Error

private def evalUnMapData (s : Stack) : List CekValue → State
  | [CekValue.VCon (Const.Data (.Map entries))] =>
      State.Return s (.VCon (.ConstPairDataList entries))
  | _ => State.Error

private def evalUnListData (s : Stack) : List CekValue → State
  | [CekValue.VCon (Const.Data (.List values))] =>
      State.Return s (.VCon (.ConstDataList values))
  | _ => State.Error

private def evalUnIData (s : Stack) : List CekValue → State
  | [CekValue.VCon (Const.Data (.I value))] =>
      State.Return s (.VCon (.Integer value))
  | _ => State.Error

private def evalUnBData (s : Stack) : List CekValue → State
  | [CekValue.VCon (Const.Data (.B value))] =>
      State.Return s (.VCon (.ByteString value))
  | _ => State.Error

def evalBuiltin (semanticsVariant : BuiltinSemanticsVariant) (s : Stack)
    (b : BuiltinFun) (Vs : List CekValue) : State :=
  match b with
  | .UnConstrData => evalUnConstrData s Vs
  | .UnMapData => evalUnMapData s Vs
  | .UnListData => evalUnListData s Vs
  | .UnIData => evalUnIData s Vs
  | .UnBData => evalUnBData s Vs
  | _ => evalBuiltinReference semanticsVariant s b Vs

/-- The fused data-destructor path is identical to the generic builtin path. -/
theorem evalBuiltin_eq_reference
    (semanticsVariant : BuiltinSemanticsVariant) (s : Stack)
    (b : BuiltinFun) (values : List CekValue) :
    evalBuiltin semanticsVariant s b values =
      evalBuiltinReference semanticsVariant s b values := by
  cases b <;> simp only [evalBuiltin]
  all_goals try rfl
  all_goals
    cases values with
    | nil => rfl
    | cons value rest =>
        cases rest with
        | cons _ _ =>
            simp [evalUnConstrData, evalUnMapData, evalUnListData,
              evalUnIData, evalUnBData, evalBuiltinReference,
              evaluateBuiltinFunction,
              PlutusCore.UPLC.BuiltinFunctions.Data.unConstrData,
              PlutusCore.UPLC.BuiltinFunctions.Data.unMapData,
              PlutusCore.UPLC.BuiltinFunctions.Data.unListData,
              PlutusCore.UPLC.BuiltinFunctions.Data.unIData,
              PlutusCore.UPLC.BuiltinFunctions.Data.unBData]
        | nil =>
            cases value with
            | VBuiltin _ _ _ => rfl
            | VDelay _ _ => rfl
            | VLam _ _ _ => rfl
            | VConstr _ _ => rfl
            | VCon constant =>
                cases constant <;> try rfl
                rename_i data
                cases data <;> rfl

open UPLC.Builtins
open ExpectedBuiltinArgs
open BuiltinNotations

private def folding (xs : List CekValue) (init : Stack) : Stack :=
  match xs with
  | [] => init
  | x :: xs' => Frame.LeftApplicationToValue x :: folding xs' init

def stepReference (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) : State :=
  match Sigma with
  | State.Eval s ρ (Term.Var x) =>
      ifBoundOtherwiseError s ρ x
  | State.Eval s ρ (Term.Term.Const c) =>
      State.Return s (CekValue.VCon c)
  | State.Eval s ρ (Term.Lam x M) =>
      State.Return s (CekValue.VLam x M ρ)
  | State.Eval s ρ (Term.Delay M) =>
      State.Return s (CekValue.VDelay M ρ)
  | State.Eval s ρ (Term.Force M) =>
      State.Eval (Frame.ForceFrame :: s) ρ M
  | State.Eval s ρ (Term.Apply M N) =>
      State.Eval (Frame.LeftApplicationToTerm N ρ :: s) ρ M
  | State.Eval s ρ (Term.Constr i (M :: Ms)) =>
      State.Eval (Frame.ConstructorArgument i [] Ms ρ :: s) ρ M
  | State.Eval s ρ (Term.Constr i []) =>
      State.Return s (CekValue.VConstr i [])
  | State.Eval s ρ (Term.Case N Ms) =>
      State.Eval (Frame.CaseScrutinee Ms ρ :: s) ρ N
  | State.Eval s ρ (Term.Builtin b) =>
      State.Return s (CekValue.VBuiltin b [] (α(b)))
  | State.Eval s ρ Term.Error =>
      State.Error
  | State.Return [] V =>
      State.Halt V
  | State.Return (Frame.LeftApplicationToTerm M ρ :: s) V =>
      State.Eval (Frame.RightApplicationOfValue V :: s) ρ M
  | State.Return (Frame.RightApplicationOfValue (CekValue.VLam x M ρ) :: s) V =>
      State.Eval s (.NonEmptyEnvironment ρ x V) M
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VLam x M ρ) =>
      State.Eval s (.NonEmptyEnvironment ρ x V) M
  | State.Return (Frame.RightApplicationOfValue (CekValue.VBuiltin b Vs (ι ⊙ η)) :: s) V =>
      ifArgVOtherwiseError (State.Return s (CekValue.VBuiltin b (V :: Vs) η)) ι
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VBuiltin b Vs (ι ⊙ η)) =>
      ifArgVOtherwiseError (State.Return s (CekValue.VBuiltin b (V :: Vs) η)) ι
  | State.Return (Frame.RightApplicationOfValue (CekValue.VBuiltin b Vs (a[ι])) :: s) V =>
      ifArgVOtherwiseError (evalBuiltinReference semanticsVariant s b (V :: Vs)) ι -- considering args reversal when calling builtin
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VBuiltin b Vs (a[ι])) =>
      ifArgVOtherwiseError (evalBuiltinReference semanticsVariant s b (V :: Vs)) ι -- considering args reversal when calling builtin
  | State.Return (Frame.ForceFrame :: s) (CekValue.VDelay M ρ) =>
      State.Eval s ρ M
  | State.Return (Frame.ForceFrame :: s) (CekValue.VBuiltin b Vs (ι ⊙ η)) =>
      ifArgQOtherwiseError (State.Return s (CekValue.VBuiltin b Vs η)) ι
  | State.Return (Frame.ForceFrame :: s) (CekValue.VBuiltin b Vs (a[ι])) =>
      ifArgQOtherwiseError (evalBuiltinReference semanticsVariant s b Vs) ι
  | State.Return (Frame.ConstructorArgument i Vs (M :: Ms) ρ :: s) V =>
      State.Eval (Frame.ConstructorArgument i (V :: Vs) Ms ρ :: s) ρ M
  | State.Return (Frame.ConstructorArgument i Vs [] ρ :: s) V =>
      State.Return s (CekValue.VConstr i (List.reverse (V :: Vs)))
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VConstr i Vs) =>
        match Ms[i]? with
        | some mi => State.Eval (folding Vs s) ρ mi
        | none => State.Error
  -- case on built-in constant types
  -- Ref: CaseBuiltin DefaultUni in plutus-core/src/PlutusCore/Default/Universe.hs
  -- The Haskell CEK dispatches via `caseBuiltin` which returns HeadOnly (no spine args)
  -- or HeadSpine (branch + args to apply). We inline that dispatch here.

  -- DefaultUniInteger: selects branch at index n (0-indexed), no spine args.
  --   | 0 <= x && x < toInteger len -> HeadOnly $ branches Vector.! fromInteger x
  --   | otherwise -> HeadError
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.Integer n)) =>
        if 0 ≤ n && n.toNat < Ms.length then
          match Ms[n.toNat]? with
          | some mi => State.Eval s ρ mi
          | none => State.Error
        else State.Error

  -- DefaultUniBool:
  --   False | len == 1 || len == 2 -> HeadOnly (branches ! 0)
  --   True  | len == 2             -> HeadOnly (branches ! 1)
  --   _ -> HeadError (wrong number of branches)
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.Bool false)) =>
        if Ms.length == 1 || Ms.length == 2 then
          match Ms[0]? with
          | some mi => State.Eval s ρ mi
          | none => State.Error
        else State.Error
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.Bool true)) =>
        if Ms.length == 2 then
          match Ms[1]? with
          | some mi => State.Eval s ρ mi
          | none => State.Error
        else State.Error

  -- DefaultUniUnit: exactly 1 branch; HeadOnly (branches ! 0), no spine args
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon Const.Unit) =>
        if Ms.length == 1 then
          match Ms[0]? with
          | some mi => State.Eval s ρ mi
          | none => State.Error
        else State.Error

  -- DefaultUniPair: exactly 1 branch; HeadSpine (branches ! 0) [fst, snd]
  --   branch is applied to fst and snd as separate arguments
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.Pair p)) =>
        if Ms.length == 1 then
          let Vs := [CekValue.VCon p.1, CekValue.VCon p.2]
          match Ms[0]? with
          | some mi => State.Eval (folding Vs s) ρ mi
          | none => State.Error
        else State.Error
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.PairData p)) =>
        if Ms.length == 1 then
          let Vs := [CekValue.VCon (Const.Data p.1), CekValue.VCon (Const.Data p.2)]
          match Ms[0]? with
          | some mi => State.Eval (folding Vs s) ρ mi
          | none => State.Error
        else State.Error

  -- DefaultUniList (len == 2):
  --   non-empty: HeadSpine (branches ! 0) [head, tail]
  --   empty:     HeadOnly  (branches ! 1), no spine args
  -- DefaultUniList (len == 1): only non-empty valid; empty → HeadError
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstList (c :: cs))) =>
        if Ms.length == 1 || Ms.length == 2 then
          let Vs := [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)]
          match Ms[0]? with
          | some mi => State.Eval (folding Vs s) ρ mi
          | none => State.Error
        else State.Error
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstList [])) =>
        if Ms.length == 2 then
          match Ms[1]? with
          | some mi => State.Eval s ρ mi
          | none => State.Error
        else State.Error
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstDataList (c :: cs))) =>
        if Ms.length == 1 || Ms.length == 2 then
          let Vs := [CekValue.VCon (.Data c), CekValue.VCon (Const.ConstDataList cs)]
          match Ms[0]? with
          | some mi => State.Eval (folding Vs s) ρ mi
          | none => State.Error
        else State.Error
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstDataList [])) =>
        if Ms.length == 2 then
          match Ms[1]? with
          | some mi => State.Eval s ρ mi
          | none => State.Error
        else State.Error
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstPairDataList (c :: cs))) =>
        if Ms.length == 1 || Ms.length == 2 then
          let Vs := [CekValue.VCon (.PairData c), CekValue.VCon (Const.ConstPairDataList cs)]
          match Ms[0]? with
          | some mi => State.Eval (folding Vs s) ρ mi
          | none => State.Error
        else State.Error
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstPairDataList [])) =>
        if Ms.length == 2 then
          match Ms[1]? with
          | some mi => State.Eval s ρ mi
          | none => State.Error
        else State.Error

  | _ => State.Error

/-!
The executable CEK transition above follows the reference semantics literally,
but Lean compiles its nested patterns into one large matcher.  A symbolic leaf
inside an otherwise concrete state therefore makes the whole transition look
symbolic to weak-head reduction.  The helpers below express the same dispatch as
a hierarchy.  Each layer consumes one known constructor before inspecting the
next value, so symbolic evaluation reaches the actual symbolic leaf without
expanding every unrelated CEK alternative.
-/

private def stepEval (s : Stack) (ρ : Environment) : Term → State
  | Term.Var x => ifBoundOtherwiseError s ρ x
  | Term.Term.Const c => State.Return s (CekValue.VCon c)
  | Term.Lam x M => State.Return s (CekValue.VLam x M ρ)
  | Term.Delay M => State.Return s (CekValue.VDelay M ρ)
  | Term.Force M => State.Eval (Frame.ForceFrame :: s) ρ M
  | Term.Apply M N => State.Eval (Frame.LeftApplicationToTerm N ρ :: s) ρ M
  | Term.Constr i terms =>
      match terms with
      | M :: Ms => State.Eval (Frame.ConstructorArgument i [] Ms ρ :: s) ρ M
      | [] => State.Return s (CekValue.VConstr i [])
  | Term.Case N Ms => State.Eval (Frame.CaseScrutinee Ms ρ :: s) ρ N
  | Term.Builtin b => State.Return s (CekValue.VBuiltin b [] (α(b)))
  | Term.Error => State.Error

private def stepBuiltinValue
    (semanticsVariant : BuiltinSemanticsVariant) (s : Stack)
    (b : BuiltinFun) (Vs : List CekValue) (expected : ExpectedBuiltinArgs)
    (V : CekValue) : State :=
  match expected with
  | ExpectedBuiltinArgs.More ι η =>
      ifArgVOtherwiseError (State.Return s (CekValue.VBuiltin b (V :: Vs) η)) ι
  | ExpectedBuiltinArgs.One ι =>
      ifArgVOtherwiseError (evalBuiltin semanticsVariant s b (V :: Vs)) ι

private def stepBuiltinForce
    (semanticsVariant : BuiltinSemanticsVariant) (s : Stack)
    (b : BuiltinFun) (Vs : List CekValue) (expected : ExpectedBuiltinArgs) : State :=
  match expected with
  | ExpectedBuiltinArgs.More ι η =>
      ifArgQOtherwiseError (State.Return s (CekValue.VBuiltin b Vs η)) ι
  | ExpectedBuiltinArgs.One ι =>
      ifArgQOtherwiseError (evalBuiltin semanticsVariant s b Vs) ι

private def stepCaseConst
    (Ms : List Term) (ρ : Environment) (s : Stack) : Const → State
  | Const.Integer n =>
      if 0 ≤ n && n.toNat < Ms.length then
        match Ms[n.toNat]? with
        | some mi => State.Eval s ρ mi
        | none => State.Error
      else State.Error
  | Const.Bool b =>
      match b with
      | false =>
          if Ms.length == 1 || Ms.length == 2 then
            match Ms[0]? with
            | some mi => State.Eval s ρ mi
            | none => State.Error
          else State.Error
      | true =>
          if Ms.length == 2 then
            match Ms[1]? with
            | some mi => State.Eval s ρ mi
            | none => State.Error
          else State.Error
  | Const.Unit =>
      if Ms.length == 1 then
        match Ms[0]? with
        | some mi => State.Eval s ρ mi
        | none => State.Error
      else State.Error
  | Const.Pair p =>
      if Ms.length == 1 then
        let Vs := [CekValue.VCon p.1, CekValue.VCon p.2]
        match Ms[0]? with
        | some mi => State.Eval (folding Vs s) ρ mi
        | none => State.Error
      else State.Error
  | Const.PairData p =>
      if Ms.length == 1 then
        let Vs := [CekValue.VCon (Const.Data p.1), CekValue.VCon (Const.Data p.2)]
        match Ms[0]? with
        | some mi => State.Eval (folding Vs s) ρ mi
        | none => State.Error
      else State.Error
  | Const.ConstList values =>
      match values with
      | c :: cs =>
          if Ms.length == 1 || Ms.length == 2 then
            let Vs := [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)]
            match Ms[0]? with
            | some mi => State.Eval (folding Vs s) ρ mi
            | none => State.Error
          else State.Error
      | [] =>
          if Ms.length == 2 then
            match Ms[1]? with
            | some mi => State.Eval s ρ mi
            | none => State.Error
          else State.Error
  | Const.ConstDataList values =>
      match values with
      | c :: cs =>
          if Ms.length == 1 || Ms.length == 2 then
            let Vs := [CekValue.VCon (.Data c), CekValue.VCon (Const.ConstDataList cs)]
            match Ms[0]? with
            | some mi => State.Eval (folding Vs s) ρ mi
            | none => State.Error
          else State.Error
      | [] =>
          if Ms.length == 2 then
            match Ms[1]? with
            | some mi => State.Eval s ρ mi
            | none => State.Error
          else State.Error
  | Const.ConstPairDataList values =>
      match values with
      | c :: cs =>
          if Ms.length == 1 || Ms.length == 2 then
            let Vs := [CekValue.VCon (.PairData c), CekValue.VCon (Const.ConstPairDataList cs)]
            match Ms[0]? with
            | some mi => State.Eval (folding Vs s) ρ mi
            | none => State.Error
          else State.Error
      | [] =>
          if Ms.length == 2 then
            match Ms[1]? with
            | some mi => State.Eval s ρ mi
            | none => State.Error
          else State.Error
  | _ => State.Error

private def stepCase
    (Ms : List Term) (ρ : Environment) (s : Stack) : CekValue → State
  | CekValue.VConstr i Vs =>
      match Ms[i]? with
      | some mi => State.Eval (folding Vs s) ρ mi
      | none => State.Error
  | CekValue.VCon c => stepCaseConst Ms ρ s c
  | _ => State.Error

private def stepFrame
    (semanticsVariant : BuiltinSemanticsVariant)
    (frame : Frame) (s : Stack) (V : CekValue) : State :=
  match frame with
  | Frame.LeftApplicationToTerm M ρ =>
      State.Eval (Frame.RightApplicationOfValue V :: s) ρ M
  | Frame.RightApplicationOfValue function =>
      match function with
      | CekValue.VLam x M ρ => State.Eval s (.NonEmptyEnvironment ρ x V) M
      | CekValue.VBuiltin b Vs expected =>
          stepBuiltinValue semanticsVariant s b Vs expected V
      | _ => State.Error
  | Frame.LeftApplicationToValue argument =>
      match V with
      | CekValue.VLam x M ρ => State.Eval s (.NonEmptyEnvironment ρ x argument) M
      | CekValue.VBuiltin b Vs expected =>
          stepBuiltinValue semanticsVariant s b Vs expected argument
      | _ => State.Error
  | Frame.ForceFrame =>
      match V with
      | CekValue.VDelay M ρ => State.Eval s ρ M
      | CekValue.VBuiltin b Vs expected =>
          stepBuiltinForce semanticsVariant s b Vs expected
      | _ => State.Error
  | Frame.ConstructorArgument i Vs terms ρ =>
      match terms with
      | M :: Ms => State.Eval (Frame.ConstructorArgument i (V :: Vs) Ms ρ :: s) ρ M
      | [] => State.Return s (CekValue.VConstr i (List.reverse (V :: Vs)))
  | Frame.CaseScrutinee Ms ρ => stepCase Ms ρ s V

def step (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) : State :=
  match Sigma with
  | State.Eval s ρ term => stepEval s ρ term
  | State.Return stack V =>
      match stack with
      | [] => State.Halt V
      | frame :: s => stepFrame semanticsVariant frame s V
  | State.Error => State.Error
  | State.Halt _ => State.Error

/-- The layered dispatch is extensionally identical to the original flat CEK
    transition.  This theorem is proved solely by constructor analysis. -/
theorem step_eq_reference
    (semanticsVariant : BuiltinSemanticsVariant) (state : State) :
    step semanticsVariant state = stepReference semanticsVariant state := by
  cases state with
  | Error => rfl
  | Halt value => rfl
  | Eval stack environment term =>
      cases term <;> try rfl
      case Constr tag terms => cases terms <;> rfl
  | Return stack value =>
      cases stack with
      | nil => rfl
      | cons frame stack =>
          cases frame with
          | ForceFrame =>
              cases value with
              | VBuiltin builtin values expected =>
                  cases expected with
                  | One _ =>
                      simp only [step, stepFrame, stepBuiltinForce, stepReference]
                      rw [evalBuiltin_eq_reference]
                  | More _ _ => rfl
              | _ => rfl
          | LeftApplicationToTerm term environment => rfl
          | LeftApplicationToValue argument =>
              cases value with
              | VBuiltin builtin values expected =>
                  cases expected with
                  | One _ =>
                      simp only [step, stepFrame, stepBuiltinValue, stepReference]
                      rw [evalBuiltin_eq_reference]
                  | More _ _ => rfl
              | _ => rfl
          | RightApplicationOfValue function =>
              cases function with
              | VBuiltin builtin values expected =>
                  cases expected with
                  | One _ =>
                      simp only [step, stepFrame, stepBuiltinValue, stepReference]
                      rw [evalBuiltin_eq_reference]
                  | More _ _ => rfl
              | _ => rfl
          | ConstructorArgument tag values terms environment =>
              cases terms <;> rfl
          | CaseScrutinee alternatives environment =>
              cases value with
              | VCon constant =>
                  cases constant with
                  | Bool value => cases value <;> rfl
                  | ConstList values => cases values <;> rfl
                  | ConstDataList values => cases values <;> rfl
                  | ConstPairDataList values => cases values <;> rfl
                  | _ => rfl
              | _ => rfl

-- Define Run Steps
def runStepsReference (semanticsVariant : BuiltinSemanticsVariant)
    (Sigma : State) (n : Nat) : State :=
  match n, Sigma with
  | _, State.Halt V => Sigma
  | _, State.Error => Sigma
  | 0, _ => State.Error -- change to error when num steps exhausted
  | Nat.succ n, _ =>
      runStepsReference semanticsVariant (stepReference semanticsVariant Sigma) n

def isTerminalState : State → Bool
  | State.Error => true
  | State.Halt _ => true
  | State.Eval _ _ _ => false
  | State.Return _ _ => false

def finishState (state : State) : State :=
  if isTerminalState state then state else State.Error

def finalStep (semanticsVariant : BuiltinSemanticsVariant) : State → State
  | State.Error => State.Error
  | state@(State.Halt _) => state
  | state@(State.Eval _ _ _) => finishState (step semanticsVariant state)
  | state@(State.Return _ _) => finishState (step semanticsVariant state)

/-! Keep the two live CEK constructors in separate recursive functions.  The
constructor is therefore part of the control flow rather than a symbolic
`State` argument whose dormant fields can be hoisted into a choice.  Both
zero-fuel equations are immediately `Error`; successor equations dispatch a
single literal CEK transition and recurse only on live successors. -/
mutual
  def runEvalSteps (semanticsVariant : BuiltinSemanticsVariant)
      (stack : Stack) (environment : Environment) (term : Term) : Nat → State
    | 0 => State.Error
    | Nat.succ remaining =>
        match remaining with
        | 0 => State.Error
        | Nat.succ _ =>
            match step semanticsVariant (.Eval stack environment term) with
            | State.Error => State.Error
            | next@(State.Halt _) => next
            | State.Eval nextStack nextEnvironment nextTerm =>
                runEvalSteps semanticsVariant nextStack nextEnvironment nextTerm remaining
            | State.Return nextStack nextValue =>
                runReturnSteps semanticsVariant nextStack nextValue remaining

  def runReturnSteps (semanticsVariant : BuiltinSemanticsVariant)
      (stack : Stack) (value : CekValue) : Nat → State
    | 0 => State.Error
    | Nat.succ remaining =>
        match step semanticsVariant (.Return stack value) with
        | State.Error => State.Error
        | next@(State.Halt _) => next
        | State.Eval nextStack nextEnvironment nextTerm =>
            runEvalSteps semanticsVariant nextStack nextEnvironment nextTerm remaining
        | State.Return nextStack nextValue =>
            runReturnSteps semanticsVariant nextStack nextValue remaining
end

def runSteps (semanticsVariant : BuiltinSemanticsVariant)
    (Sigma : State) (n : Nat) : State :=
  match Sigma with
  | State.Error => State.Error
  | State.Halt _ => Sigma
  | State.Eval stack environment term =>
      runEvalSteps semanticsVariant stack environment term n
  | State.Return stack value =>
      runReturnSteps semanticsVariant stack value n

theorem finishState_eq_reference_zero
    (semanticsVariant : BuiltinSemanticsVariant) (state : State) :
    finishState state = runStepsReference semanticsVariant state 0 := by
  cases state <;> rfl

theorem finalStep_eq_reference_one
    (semanticsVariant : BuiltinSemanticsVariant) (state : State) :
    finalStep semanticsVariant state =
      runStepsReference semanticsVariant state 1 := by
  cases state with
  | Error => rfl
  | Halt value => rfl
  | Eval stack environment term =>
      simp only [finalStep, runStepsReference]
      rw [step_eq_reference]
      apply finishState_eq_reference_zero
  | Return stack value =>
      simp only [finalStep, runStepsReference]
      rw [step_eq_reference]
      apply finishState_eq_reference_zero

private theorem finishState_ifBoundOtherwiseError
    (stack : Stack) (environment : Environment) (name : String) :
    finishState (ifBoundOtherwiseError stack environment name) = State.Error := by
  cases environment with
  | EmptyEnvironment => rfl
  | NonEmptyEnvironment rest boundName value =>
      simp only [ifBoundOtherwiseError]
      split
      · rfl
      · exact finishState_ifBoundOtherwiseError stack rest name
termination_by sizeOf environment

private theorem finishState_step_eval
    (semanticsVariant : BuiltinSemanticsVariant)
    (stack : Stack) (environment : Environment) (term : Term) :
    finishState (step semanticsVariant (.Eval stack environment term)) =
      State.Error := by
  cases term with
  | Var name => exact finishState_ifBoundOtherwiseError stack environment name
  | Constr tag terms => cases terms <;> rfl
  | Const constant => rfl
  | Lam name body => rfl
  | Delay body => rfl
  | Force body => rfl
  | Apply function argument => rfl
  | Case scrutinee alternatives => rfl
  | Builtin builtin => rfl
  | Error => rfl

theorem runStepsReference_eval_one
    (semanticsVariant : BuiltinSemanticsVariant)
    (stack : Stack) (environment : Environment) (term : Term) :
    runStepsReference semanticsVariant (.Eval stack environment term) 1 =
      State.Error := by
  rw [← finalStep_eq_reference_one]
  simp only [finalStep]
  exact finishState_step_eval semanticsVariant stack environment term

theorem runConstructorSteps_eq_reference
    (semanticsVariant : BuiltinSemanticsVariant) (fuel : Nat) :
    (∀ (stack : Stack) (environment : Environment) (term : Term),
      runEvalSteps semanticsVariant stack environment term fuel =
        runStepsReference semanticsVariant (.Eval stack environment term) fuel) ∧
    (∀ (stack : Stack) (value : CekValue),
      runReturnSteps semanticsVariant stack value fuel =
        runStepsReference semanticsVariant (.Return stack value) fuel) := by
  induction fuel with
  | zero =>
      constructor <;> intros <;> rfl
  | succ fuel ih =>
      constructor
      · intro stack environment term
        cases fuel with
        | zero =>
            simpa [runEvalSteps] using
              (runStepsReference_eval_one semanticsVariant stack environment term).symm
        | succ fuel =>
            simp only [runEvalSteps, runStepsReference]
            rw [← step_eq_reference semanticsVariant]
            generalize hnext : step semanticsVariant (.Eval stack environment term) = next
            cases next with
            | Error => simp [runStepsReference]
            | Halt value => simp [runStepsReference]
            | Eval nextStack nextEnvironment nextTerm =>
                exact ih.1 nextStack nextEnvironment nextTerm
            | Return nextStack nextValue => exact ih.2 nextStack nextValue
      · intro stack value
        simp only [runReturnSteps, runStepsReference]
        rw [← step_eq_reference semanticsVariant]
        generalize hnext : step semanticsVariant (.Return stack value) = next
        cases next with
        | Error => simp [runStepsReference]
        | Halt value => simp [runStepsReference]
        | Eval nextStack nextEnvironment nextTerm =>
            exact ih.1 nextStack nextEnvironment nextTerm
        | Return nextStack nextValue => exact ih.2 nextStack nextValue

/-- The live-state driver preserves the literal reference fuel semantics. -/
theorem runSteps_eq_reference
    (semanticsVariant : BuiltinSemanticsVariant) (state : State) (fuel : Nat) :
    runSteps semanticsVariant state fuel =
      runStepsReference semanticsVariant state fuel := by
  cases state with
  | Error => simp [runSteps, runStepsReference]
  | Halt value => simp [runSteps, runStepsReference]
  | Eval stack environment term =>
      simp only [runSteps]
      exact (runConstructorSteps_eq_reference semanticsVariant fuel).1
        stack environment term
  | Return stack value =>
      simp only [runSteps]
      exact (runConstructorSteps_eq_reference semanticsVariant fuel).2 stack value

-- Define Apply Params
def applyParams (body : Term) (params : List Term) : Term :=
  match params with
  | h :: t => applyParams (Term.Apply body h) t
  | [] => body

-- Define Initial State
def initialState (t : Term) : State :=
  State.Eval [] Environment.EmptyEnvironment t

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
