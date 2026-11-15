import Blaster.Optimize.Basic
import PlutusCore.UPLC.Optimize.Aiken.Validation

namespace PlutusCore.UPLC.Optimize.Aiken
open Lean Meta
open Blaster.Optimize
open PlutusCore.Default
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.Data (Data)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Small generated theorem matcher. The dispatcher below folds a literal
    compiler state to this shape only after a definitional-equality check. -/
@[blaster (register := false)]
theorem compiled_validation_rule
    (a0 a1 a2 a3 a4 a5 a6 a7 p q : CekValue) (tail : PlutusCore.UPLC.CekValue.Environment)
    (sem : BuiltinSemanticsVariant) (k : Stack) (xs : List Data) (fuel : Nat) :
    runSteps sem
      (validationEntry k (validationCaptures a0 a1 a2 a3 a4 a5 a6 a7 p q tail) xs) fuel =
      validationSummary sem k xs fuel :=
  validation_run_summary a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k xs fuel

initialize registerTraceClass `Optimize.aikenValidation

private def appArgs? (e : Expr) (name : Name) (arity : Nat) : Option (Array Expr) :=
  if e.isAppOfArity name arity then some e.getAppArgs else none

private def closedDefEq (a b : Expr) : TranslateEnvT Bool := do
  if a.hasFVar || b.hasFVar || a.hasMVar || b.hasMVar || a.hasLevelMVar || b.hasLevelMVar then return false
  isDefEq a b

private def valueArgs (n : Nat) : Expr :=
  if n ≤ 1 then mkApp (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.One)
    (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV)
  else mkApp2 (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.More)
    (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV) (valueArgs (n-1))
termination_by n

private def builtinValue (b : Name) (n : Nat) : Expr :=
  mkApp3 (mkConst ``CekValue.VBuiltin) (mkConst b)
    (mkApp (mkConst ``List.nil [.zero]) (mkConst ``CekValue)) (valueArgs n)

/-- Only closed UPLC code and builtin constants use definitional equality.
    Symbolic inputs/captures are matched structurally; the optimizer's local
    variables do not live in Lean Meta's local context. No metavariables are
    assigned and no input constraints are assumed. -/
@[blaster runSteps]
def optimizeCompiledValidation (_f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if args.size != 3 then return none
  let state := args[1]!.consumeMData
  if state.hasMVar || state.hasLevelMVar then return none
  let some fields := appArgs? state ``State.Eval 3 | return none
  let k := fields[0]!
  unless ← closedDefEq fields[2]! (mkConst ``validationBody) do return none
  let some first := appArgs? fields[1]! ``List.cons 3 | return none
  let some con := appArgs? first[1]! ``CekValue.VCon 1 | return none
  let some list := appArgs? con[0]! ``Const.ConstDataList 1 | return none
  let xs := list[0]!
  let some second := appArgs? first[2]! ``List.cons 3 | return none
  let some closure := appArgs? second[1]! ``CekValue.VLam 2 | return none
  unless ← closedDefEq closure[0]! (mkApp (mkConst ``Term.Lam) (mkConst ``validationBody)) do return none
  unless exprEq closure[1]! second[2]! || Expr.eqv closure[1]! second[2]! do return none
  let mut tail := second[2]!
  let mut captures : Array Expr := #[]
  for _ in [:15] do
    let some cell := appArgs? tail ``List.cons 3 | return none
    captures := captures.push cell[1]!
    tail := cell[2]!
  for (i, b, n) in #[(8, ``BuiltinFun.IfThenElse, 3), (11, ``BuiltinFun.ChooseList, 3),
      (12, ``BuiltinFun.MkCons, 2), (13, ``BuiltinFun.HeadList, 1), (14, ``BuiltinFun.TailList, 1)] do
    unless ← closedDefEq captures[i]! (builtinValue b n) do return none
  let params := captures[:8].toArray ++ #[captures[9]!, captures[10]!, tail]
  let caps := mkAppN (mkConst ``validationCaptures) params
  let canonical := mkApp3 (mkConst ``validationEntry) k caps xs
  trace[Optimize.aikenValidation] "folded compiled validation loop"
  blaster_opt_compiled_validation_rule _f #[args[0]!, canonical, args[2]!]

end PlutusCore.UPLC.Optimize.Aiken
