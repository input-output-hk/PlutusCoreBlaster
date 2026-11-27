import PlutusCore.UPLC.Optimize.Extension.Recognize

namespace PlutusCore.UPLC.Optimize
open Lean Meta
open Blaster.Optimize
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.Data (Data)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

open Recognize

@[blaster (register := false)]
theorem scalar_search_rule (bindings : ScalarSearch.Bindings)
    (p : ScalarSearch.Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) :
    runSteps sem (ScalarSearch.entry p bindings k xs) fuel = ScalarSearch.summary p sem k xs fuel :=
  ScalarSearch.run_summary bindings p sem k xs fuel

initialize registerTraceClass `Optimize.scalarSearch
/-- Extract the predicate and capture positions, then check the entire closed
    skeleton below. Extraction alone never authorizes a rewrite. -/
private def skeleton? (code : Expr) : Option (Expr × Nat × Nat × Nat) := do
  let force ← args? code ``Term.Force 1
  let outerCase ← args? force[0]! ``Term.Case 2
  let chooseIndex ← capIndex? (← listItem? outerCase[1]! 0)
  let outerConstr ← args? outerCase[0]! ``Term.Constr 2
  let delayed ← listItem? outerConstr[1]! 2
  let delay ← args? delayed ``Term.Delay 1
  let force ← args? delay[0]! ``Term.Force 1
  let innerCase ← args? force[0]! ``Term.Case 2
  let ifIndex ← capIndex? (← listItem? innerCase[1]! 0)
  let innerConstr ← args? innerCase[0]! ``Term.Constr 2
  let test ← listItem? innerConstr[1]! 0
  let miss ← args? (← listItem? innerConstr[1]! 2) ``Term.Delay 1
  let recurse ← args? miss[0]! ``Term.Apply 2
  let tail ← args? recurse[1]! ``Term.Apply 2
  let tailIndex ← capIndex? tail[0]!
  return (test, ifIndex, chooseIndex, tailIndex)

private def predicate? (code : Expr) : TranslateEnvT (Option (Expr × Expr × Array Nat)) := do
  let some (test, ifIndex, chooseIndex, tailIndex) := skeleton? code | return none
  let some outer := args? test ``Term.Apply 2 | return none
  let some first := args? outer[0]! ``Term.Apply 2 | return none
  let some builtin := args? first[0]! ``Term.Builtin 1 | return none
  let some decode := args? first[1]! ``Term.Apply 2 | return none
  let some head := args? decode[1]! ``Term.Apply 2 | return none
  let some headIndex := capIndex? head[0]! | return none
  let some literal := args? outer[1]! ``PlutusCore.UPLC.Term.Term.Const 1 | return none
  let (ctor, comparison, literalCtor) ←
    if builtin[0]!.isConstOf ``BuiltinFun.EqualsInteger then
      pure (``ScalarSearch.Predicate.integer, ``ScalarSearch.Comparison.eq, ``Const.Integer)
    else if builtin[0]!.isConstOf ``BuiltinFun.LessThanInteger then
      pure (``ScalarSearch.Predicate.integer, ``ScalarSearch.Comparison.lt, ``Const.Integer)
    else if builtin[0]!.isConstOf ``BuiltinFun.LessThanEqualsInteger then
      pure (``ScalarSearch.Predicate.integer, ``ScalarSearch.Comparison.le, ``Const.Integer)
    else if builtin[0]!.isConstOf ``BuiltinFun.EqualsByteString then
      pure (``ScalarSearch.Predicate.bytes, ``ScalarSearch.Comparison.eq, ``Const.ByteString)
    else if builtin[0]!.isConstOf ``BuiltinFun.LessThanByteString then
      pure (``ScalarSearch.Predicate.bytes, ``ScalarSearch.Comparison.lt, ``Const.ByteString)
    else if builtin[0]!.isConstOf ``BuiltinFun.LessThanEqualsByteString then
      pure (``ScalarSearch.Predicate.bytes, ``ScalarSearch.Comparison.le, ``Const.ByteString)
    else return none
  let some value := args? literal[0]! literalCtor 1 | return none
  let p := mkApp2 (mkConst ctor) (mkConst comparison) value[0]!
  let layout := mkAppN (mkConst ``ScalarSearch.Layout.mk)
    #[mkNatLit ifIndex, mkNatLit chooseIndex, mkNatLit headIndex, mkNatLit tailIndex]
  let test := mkApp2 (mkConst ``ScalarSearch.Predicate.test) p (mkNatLit headIndex)
  let expected := mkApp2 (mkConst ``ScalarSearch.body) layout test
  unless ← closedDefEq code expected do return none
  return some (p, layout, #[ifIndex, chooseIndex, headIndex, tailIndex])
/-- Recognizes the shared search skeleton, six scalar predicates and arbitrary
    unused captures/stack suffixes. Only closed code uses definitional equality;
    symbolic payloads are checked structurally and are never assigned. -/
@[blaster runSteps]
def optimizeScalarSearch (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if args.size != 3 then return none
  let state := args[1]!.consumeMData
  if state.hasMVar || state.hasLevelMVar then return none
  let some fields := args? state ``State.Eval 3 | return none
  let some (p, layout, indices) ← predicate? fields[2]! | return none
  let some first := args? fields[1]! ``List.cons 3 | return none
  let some con := args? first[1]! ``CekValue.VCon 1 | return none
  let some list := args? con[0]! ``Const.ConstDataList 1 | return none
  let some second := args? first[2]! ``List.cons 3 | return none
  let some closure := args? second[1]! ``CekValue.VLam 2 | return none
  unless ← closedDefEq closure[0]! (mkApp (mkConst ``Term.Lam) fields[2]!) do return none
  unless exprEq closure[1]! second[2]! || Expr.eqv closure[1]! second[2]! do return none
  let some bindings ← certifyBindings second[2]! layout indices | return none
  let canonical := mkAppN (mkConst ``ScalarSearch.entry) #[p, bindings, fields[0]!, list[0]!]
  trace[Optimize.scalarSearch] "folded scalar search {p}"
  blaster_opt_scalar_search_rule f #[args[0]!, canonical, args[2]!]

end PlutusCore.UPLC.Optimize
