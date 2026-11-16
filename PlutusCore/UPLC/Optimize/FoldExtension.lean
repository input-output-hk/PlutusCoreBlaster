import PlutusCore.UPLC.Optimize.Extension
import PlutusCore.UPLC.Optimize.CallbackCompiler

namespace PlutusCore.UPLC.Optimize
open Lean Meta Blaster.Optimize
open PlutusCore.Default PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

@[blaster (register := false)]
theorem compiled_fold_rule (kind : CompiledFold.Kind) (b : CompiledFold.Bindings)
    (callback : PlutusCore.UPLC.Term.Term) (sem : BuiltinSemanticsVariant)
    (compiled : CompiledFold.CompiledCallback kind b callback sem)
    (k : Stack) (acc : Int) (xs : List kind.Item) (fuel : Nat) :
    runSteps sem (CompiledFold.start compiled k acc xs) fuel =
      CompiledFold.summary compiled k acc xs fuel :=
  CompiledFold.run_summary compiled k acc xs fuel

initialize registerTraceClass `Optimize.compiledFold

private def app? (e : Expr) (name : Name) (n : Nat) : Option (Array Expr) :=
  if e.isAppOfArity name n then some e.getAppArgs else none

private def item? (e : Expr) (index : Nat) : Option Expr := do
  let cell ← app? e ``List.cons 3
  match index with
  | 0 => some cell[1]!
  | n + 1 => item? cell[2]! n

private def slot? (e : Expr) : Option Nat := do
  let v ← app? e ``Term.Var 1
  let .lit (.natVal n) := v[0]! | none
  if n < 3 then none else some (n - 3)

private def shape? (code : Expr) : Option (Expr × Nat × Nat) := do
  let force ← app? code ``Term.Force 1
  let outer ← app? force[0]! ``Term.Case 2
  let choose ← slot? (← item? outer[1]! 0)
  let ctor ← app? outer[0]! ``Term.Constr 2
  let delayed ← app? (← item? ctor[1]! 2) ``Term.Delay 1
  let inner ← app? delayed[0]! ``Term.Case 2
  let args ← app? inner[0]! ``Term.Constr 2
  let tailCall ← app? (← item? args[1]! 1) ``Term.Apply 2
  let tail ← slot? tailCall[0]!
  return (← item? args[1]! 2, choose, tail)

private def builtin (name : Name) (arity : Nat) : Expr :=
  let arg := mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV
  let rec types : Nat → Expr
    | 0 => mkApp (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.One) arg
    | n + 1 => mkApp2 (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.More) arg (types n)
  mkApp3 (mkConst ``CekValue.VBuiltin) (mkConst name)
    (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``CekValue)) (types (arity - 1))

@[blaster runSteps]
def optimizeCompiledFold (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := withLocalContext do
  if args.size != 3 || args[1]!.hasMVar then return none
  let some state := app? args[1]!.consumeMData ``State.Eval 3 | return none
  if state[2]!.hasFVar then return none
  let some (callback, choose, tail) := shape? state[2]! | return none
  let code := mkAppN (mkConst ``CompiledFold.body)
    #[mkNatLit choose, mkNatLit tail, callback]
  unless ← isDefEq code state[2]! do return none
  let some first := app? state[1]! ``List.cons 3 | return none
  let some accBox := app? first[1]! ``CekValue.VCon 1 | return none
  let some acc := app? accBox[0]! ``Const.Integer 1 | return none
  let some second := app? first[2]! ``List.cons 3 | return none
  let some listBox := app? second[1]! ``CekValue.VCon 1 | return none
  let (kind, xs) ←
    if let some list := app? listBox[0]! ``Const.ConstDataList 1 then
      pure (mkConst ``CompiledFold.Kind.data, list[0]!)
    else if let some list := app? listBox[0]! ``Const.ConstPairDataList 1 then
      pure (mkConst ``CompiledFold.Kind.pair, list[0]!)
    else return none
  let some third := app? second[2]! ``List.cons 3 | return none
  let some closure := app? third[1]! ``CekValue.VLam 2 | return none
  unless ← isDefEq closure[0]! (mkApp (mkConst ``Term.Lam) (mkApp (mkConst ``Term.Lam) code)) do return none
  unless ← isDefEq closure[1]! third[2]! do return none
  let env := third[2]!
  let mut proofs := #[]
  for (index, name, arity) in #[(choose, ``BuiltinFun.ChooseList, 3), (tail, ``BuiltinFun.TailList, 1)] do
    let some value := item? env index | return none
    let expected := builtin name arity
    unless ← isDefEq value expected do return none
    proofs := proofs.push (← mkEqRefl (← mkAppM ``Option.some #[expected]))
  let b := mkAppN (mkConst ``CompiledFold.Bindings.mk)
    #[env, mkNatLit choose, mkNatLit tail, proofs[0]!, proofs[1]!]
  let saved : Lean.Meta.SavedState ← liftM (Lean.Meta.saveState)
  try
    let compiled ← CallbackCompiler.compile kind b callback args[0]!
    let canonical := mkAppN (mkConst ``CompiledFold.start)
      #[kind, b, callback, args[0]!, compiled, state[0]!, acc[0]!, xs]
    unless ← isDefEq canonical args[1]! do throwError "fold entry differs from recognized source"
    trace[Optimize.compiledFold] "compiled callback and certified fold"
    let plan := compiled.getAppArgs[4]!
    let rhs := mkAppN (mkConst ``CompiledFold.dataSummary)
      #[kind, args[0]!, plan, state[0]!, acc[0]!, xs, args[2]!]
    let proof := mkAppN (mkConst ``compiled_fold_rule)
      #[kind, b, callback, args[0]!, compiled, state[0]!, acc[0]!, xs, args[2]!]
    CallbackCompiler.checkRewrite proof (← mkEq (mkAppN f args) rhs)
    return some (← hashcons rhs)
  catch e =>
    let _ ← (saved.restore : MetaM Unit)
    trace[Optimize.compiledFold] "declined callback: {e.toMessageData}"
    return none

end PlutusCore.UPLC.Optimize
