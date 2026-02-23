import PlutusCore.Default
import PlutusCore.UPLC.Builtins
import PlutusCore.UPLC.BuiltinFunctions.Evaluate
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
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

def evalBuiltin (semanticsVariant : BuiltinSemanticsVariant) (s : Stack) (b : BuiltinFun) (Vs : List CekValue) : State :=
  match UPLC.Evaluate.evaluateBuiltinFunction semanticsVariant b Vs with
  | some V => State.Return s V
  | none => State.Error

open UPLC.Builtins
open ExpectedBuiltinArgs
open BuiltinNotations

def step (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) : State :=
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
      ifArgVOtherwiseError (State.Return s (CekValue.VBuiltin b (V :: Vs) η)) ι
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VBuiltin b Vs (ι ⊙ η)) =>
      ifArgVOtherwiseError (State.Return s (CekValue.VBuiltin b (V :: Vs) η)) ι
  | State.Return (Frame.RightApplicationOfValue (CekValue.VBuiltin b Vs (a[ι])) :: s) V =>
      ifArgVOtherwiseError (evalBuiltin semanticsVariant s b (V :: Vs)) ι -- considering args reversal when calling builtin
  | State.Return (Frame.LeftApplicationToValue V :: s) (CekValue.VBuiltin b Vs (a[ι])) =>
      ifArgVOtherwiseError (evalBuiltin semanticsVariant s b (V :: Vs)) ι -- considering args reversal when calling builtin
  | State.Return (Frame.ForceFrame :: s) (CekValue.VDelay M ρ) =>
      State.Eval s ρ M
  | State.Return (Frame.ForceFrame :: s) (CekValue.VBuiltin b Vs (ι ⊙ η)) =>
      ifArgQOtherwiseError (State.Return s (CekValue.VBuiltin b Vs η)) ι
  | State.Return (Frame.ForceFrame :: s) (CekValue.VBuiltin b Vs (a[ι])) =>
      ifArgQOtherwiseError (evalBuiltin semanticsVariant s b Vs) ι
  | State.Return (Frame.ConstructorArgument i Vs (M :: Ms) ρ :: s) V =>
      State.Eval (Frame.ConstructorArgument i (V :: Vs) Ms ρ :: s) ρ M
  | State.Return (Frame.ConstructorArgument i Vs [] ρ :: s) V =>
      State.Return s (CekValue.VConstr i (List.reverse (V :: Vs)))
  | State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VConstr i Vs) =>
        match List.get?Internal Ms i with
        | some mi => State.Eval (folding Vs s) ρ mi
        | none => State.Error
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
  State.Eval [] Environment.EmptyEnvironment t

def cekExecuteProgramWithSemanticVariant (semanticVariant : BuiltinSemanticsVariant) (p : Program) (params : List Term) (n : Nat) : State :=
  match p with
  | Program.Program _ body =>
      runSteps semanticVariant (initialState (applyParams body params)) n

-- Define CEK Execution
def cekExecuteProgram : Program → List Term →  Nat → State := cekExecuteProgramWithSemanticVariant default

set_option linter.unusedVariables true

end PlutusCore.UPLC.CekMachine
