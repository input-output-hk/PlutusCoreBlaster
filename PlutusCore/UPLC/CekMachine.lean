import PlutusCore.UPLC.Builtins
import PlutusCore.UPLC.BuiltinFunctions.Evaluate
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Evaluate
open PlutusCore.UPLC.Term

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

-- Define Helper Functions
-- Define ifBoundOtherwiseError
def ifBoundOtherwiseError (s : Stack) (p : Environment) (x : String) : State :=
  match p with
  | Environment.EmptyEnvironment => State.Error
  | Environment.NonEmptyEvironment p' x' V =>
      if x == x' then State.Return s V else ifBoundOtherwiseError s p' x

-- Define ifArgVOtherwiseError
def ifArgVOtherwiseError (Sigma : State) (l : ExpectedBuiltinArg) : State :=
  match l with
  | ExpectedBuiltinArg.ArgV => Sigma
  | ExpectedBuiltinArg.ArgQ => State.Error

def ifArgQOtherwiseError (Sigma : State) (l : ExpectedBuiltinArg) : State :=
  match l with
  | ExpectedBuiltinArg.ArgQ => Sigma
  | ExpectedBuiltinArg.ArgV => State.Error

def unfoldCase (s : Stack) (i : Nat) (Ms : List Term) (Vs : List CekValue) (p : Environment) : State :=
  match Ms[i]? with
  | some mi =>
      let sOut := Vs.foldr (fun V sAcc => Frame.LeftApplicationToValue V :: sAcc) s
      State.Eval sOut p mi
  | none => State.Error

def evalBuiltin (s : Stack) (b : BuiltinFun) (Vs : List CekValue) : State :=
  match UPLC.Evaluate.evaluateBuiltinFunction b Vs with
  | some V => State.Return s V
  | none => State.Error

open UPLC.Builtins
open ExpectedBuiltinArgs
open BuiltinNotations

def step (Sigma : State) : State :=
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
      State.Eval s (Environment.NonEmptyEvironment ρ x V) M
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VLam x M ρ) =>
      State.Eval s (Environment.NonEmptyEvironment ρ x V) M
  | State.Return (Frame.RightApplicationOfValue (CekValue.VBuiltin b Vs (ι ⊙ η)) :: s) V =>
      ifArgVOtherwiseError (State.Return s (CekValue.VBuiltin b (Vs ++ [V]) η)) ι
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VBuiltin b Vs (ι ⊙ η)) =>
      ifArgVOtherwiseError (State.Return s (CekValue.VBuiltin b (Vs ++ [V]) η)) ι
  | State.Return (Frame.RightApplicationOfValue (CekValue.VBuiltin b Vs (a[ι])) :: s) V =>
      ifArgVOtherwiseError (evalBuiltin s b (Vs ++ [V])) ι
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VBuiltin b Vs (a[ι])) =>
      ifArgVOtherwiseError (evalBuiltin s b (Vs ++ [V])) ι
  | State.Return (Frame.ForceFrame :: s) (CekValue.VDelay M ρ) =>
      State.Eval s ρ M
  | State.Return (Frame.ForceFrame :: s) (CekValue.VBuiltin b Vs (ι ⊙ η)) =>
      ifArgQOtherwiseError (State.Return s (CekValue.VBuiltin b Vs η)) ι
  | State.Return (Frame.ForceFrame :: s) (CekValue.VBuiltin b Vs (a[ι])) =>
      ifArgQOtherwiseError (evalBuiltin s b Vs) ι
  | State.Return (Frame.ConstructorArgument i Vs (M :: Ms) ρ :: s) V =>
      State.Eval (Frame.ConstructorArgument i (Vs ++ [V]) Ms ρ :: s) ρ M
  | State.Return (Frame.ConstructorArgument i Vs [] ρ :: s) V =>
      State.Return s (CekValue.VConstr i (Vs ++ [V]))
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VConstr i Vs) =>
      unfoldCase s i Ms Vs ρ
  | _ => State.Error

-- Define Run Steps
def runSteps (Sigma : State) (n : Nat) : State :=
  match n, Sigma with
  | _, State.Halt V => Sigma
  | _, State.Error => Sigma
  | 0, _ => State.Error -- change to error when num steps exhausted
  | Nat.succ n, _ => runSteps (step Sigma) n

-- Define Apply Params
def applyParams (body : Term) (params : List Term) : Term :=
  match params with
  | h :: t => applyParams (Term.Apply body h) t
  | [] => body

-- Define Initial State
def initialState (t : Term) : State :=
  State.Eval [] Environment.EmptyEnvironment t

-- Define CEK Execution
def cekExecuteProgram (p : Program) (params : List Term) (n : Nat) : State :=
  match p with
  | Program.Program _ body =>
      -- considering all UPLC version
      -- TODO: consider version when evaluating builtins
      runSteps (initialState (applyParams body params)) n

set_option linter.unusedVariables true

end PlutusCore.UPLC.CekMachine
