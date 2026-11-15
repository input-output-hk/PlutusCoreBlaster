import PlutusCore.UPLC.Optimize.Extension.Recognize
import PlutusCore.UPLC.Optimize.ByteTraversal

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

attribute [blaster] execute_traversal

@[blaster (register := false)]
theorem byte_traversal_rule (bindings : ByteTraversal.Bindings)
    (p : ByteTraversal.Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) :
    runSteps sem (ByteTraversal.entry p bindings k xs) fuel = ByteTraversal.summary p sem k xs fuel :=
  ByteTraversal.run_summary bindings p sem k xs fuel

initialize registerTraceClass `Optimize.byteTraversal
private def bytePredicate? (code : Expr) : TranslateEnvT (Option (Expr × Expr × Nat × Array Nat)) := do
  let some force := args? code ``Term.Force 1 | return none
  let some outerCase := args? force[0]! ``Term.Case 2 | return none
  let some chooseTerm := listItem? outerCase[1]! 0 | return none
  let some chooseIndex := capIndex? chooseTerm | return none
  let some outerConstr := args? outerCase[0]! ``Term.Constr 2 | return none
  let some delayed := listItem? outerConstr[1]! 2 | return none
  let some delay := args? delayed ``Term.Delay 1 | return none
  let some application := args? delay[0]! ``Term.Apply 2 | return none
  let some decode := args? application[1]! ``Term.Apply 2 | return none
  let some head := args? decode[1]! ``Term.Apply 2 | return none
  let some headIndex := capIndex? head[0]! | return none
  let some lambda := args? application[0]! ``Term.Lam 1 | return none
  let some force := args? lambda[0]! ``Term.Force 1 | return none
  let some innerCase := args? force[0]! ``Term.Case 2 | return none
  let some ifTerm := listItem? innerCase[1]! 0 | return none
  let some ifIndex := capIndexFrom? 3 ifTerm | return none
  let some innerConstr := args? innerCase[0]! ``Term.Constr 2 | return none
  let some test := listItem? innerConstr[1]! 0 | return none
  let some testApply := args? test ``Term.Apply 2 | return none
  let some testFirst := args? testApply[0]! ``Term.Apply 2 | return none
  let some comparator := args? testFirst[0]! ``Term.Builtin 1 | return none
  let comparison ←
    if comparator[0]!.isConstOf ``BuiltinFun.EqualsInteger then pure ``ScalarSearch.Comparison.eq
    else if comparator[0]!.isConstOf ``BuiltinFun.LessThanInteger then pure ``ScalarSearch.Comparison.lt
    else if comparator[0]!.isConstOf ``BuiltinFun.LessThanEqualsInteger then pure ``ScalarSearch.Comparison.le
    else return none
  let some constant := args? testFirst[1]! ``PlutusCore.UPLC.Term.Term.Const 1 | return none
  let some bound := args? constant[0]! ``Const.Integer 1 | return none
  let some success := listItem? innerConstr[1]! 1 | return none
  let some delayedSuccess := args? success ``Term.Delay 1 | return none
  let some successApply := args? delayedSuccess[0]! ``Term.Apply 2 | return none
  let some consApply := args? successApply[0]! ``Term.Apply 2 | return none
  let some consIndex := capIndexFrom? 3 consApply[0]! | return none
  let some recurse := args? successApply[1]! ``Term.Apply 2 | return none
  let some tail := args? recurse[1]! ``Term.Apply 2 | return none
  let some tailIndex := capIndexFrom? 3 tail[0]! | return none
  let p := mkApp2 (mkConst ``ByteTraversal.Predicate.mk) (mkConst comparison) bound[0]!
  let layout := mkAppN (mkConst ``ScalarSearch.Layout.mk)
    #[mkNatLit ifIndex, mkNatLit chooseIndex, mkNatLit headIndex, mkNatLit tailIndex]
  let expected := mkAppN (mkConst ``ByteTraversal.body)
    #[layout, mkNatLit consIndex, mkApp (mkConst ``ByteTraversal.Predicate.test) p]
  unless ← closedDefEq code expected do return none
  return some (p, layout, consIndex, #[ifIndex, chooseIndex, headIndex, tailIndex])
/-- Checked byte-list traversals use the same arbitrary-layout binding
    certificates and shared induction as searches. No Cardano-specific sizes
    or context projections are built into recognition. -/
@[blaster runSteps]
def optimizeByteTraversal (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if args.size != 3 then return none
  let state := args[1]!.consumeMData
  if state.hasMVar || state.hasLevelMVar then return none
  let some fields := args? state ``State.Eval 3 | return none
  let some (p, layout, consIndex, indices) ← bytePredicate? fields[2]! | return none
  let some first := args? fields[1]! ``List.cons 3 | return none
  let some con := args? first[1]! ``CekValue.VCon 1 | return none
  let some list := args? con[0]! ``Const.ConstDataList 1 | return none
  let some second := args? first[2]! ``List.cons 3 | return none
  let some closure := args? second[1]! ``CekValue.VLam 2 | return none
  unless ← closedDefEq closure[0]! (mkApp (mkConst ``Term.Lam) fields[2]!) do return none
  unless exprEq closure[1]! second[2]! || Expr.eqv closure[1]! second[2]! do return none
  let env := second[2]!
  let some base ← certifyBindings env layout indices | return none
  let some actual := listItem? env consIndex | return none
  let expected := builtinValue ``BuiltinFun.MkCons 2
  unless ← closedDefEq actual expected do return none
  let someValue := mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``CekValue) expected
  let proof ← mkEqRefl someValue
  let bindings := mkApp3 (mkConst ``ByteTraversal.Bindings.mk) base (mkNatLit consIndex) proof
  let canonical := mkAppN (mkConst ``ByteTraversal.entry) #[p, bindings, fields[0]!, list[0]!]
  trace[Optimize.byteTraversal] "folded checked byte traversal {p}"
  blaster_opt_byte_traversal_rule f #[args[0]!, canonical, args[2]!]

end PlutusCore.UPLC.Optimize
