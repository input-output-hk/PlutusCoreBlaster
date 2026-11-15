import Blaster.Optimize.Basic
import PlutusCore.UPLC.Optimize.Administrative
import PlutusCore.UPLC.Optimize.Composition
import PlutusCore.UPLC.Optimize.ScalarSearch
import PlutusCore.UPLC.Optimize.ByteTraversal
import PlutusCore.UPLC.Optimize.Prefix

/-! Opt-in, validator-independent PR472 rules. No Aiken fixture is imported. -/
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

attribute [blaster] Administrative.apply_lambda Administrative.force_delay
  Administrative.return_lambda Administrative.return_lambda_left
  Administrative.lookup_tail Administrative.lookup_head Administrative.return_empty

attribute [blaster] Composition.execute_empty Composition.execute_identity
  Composition.execute_constant Composition.execute_assert

attribute [blaster] execute_traversal Composition.conditional_tail

@[blaster (register := false)]
theorem scalar_search_rule (bindings : ScalarSearch.Bindings)
    (p : ScalarSearch.Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) :
    runSteps sem (ScalarSearch.entry p bindings k xs) fuel = ScalarSearch.summary p sem k xs fuel :=
  ScalarSearch.run_summary bindings p sem k xs fuel

initialize registerTraceClass `Optimize.scalarSearch

private def args? (e : Expr) (name : Name) (arity : Nat) : Option (Array Expr) :=
  if e.isAppOfArity name arity then some e.getAppArgs else none

private def listItem? (e : Expr) (index : Nat) : Option Expr := do
  let cell ← args? e ``List.cons 3
  match index with
  | 0 => some cell[1]!
  | n + 1 => listItem? cell[2]! n

private def capIndexFrom? (binderCount : Nat) (e : Expr) : Option Nat := do
  let v ← args? e ``Term.Var 1
  let .lit (.natVal n) := v[0]! | none
  if n < binderCount then none else some (n - binderCount)

private def capIndex? (e : Expr) : Option Nat := capIndexFrom? 2 e

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

private def closedDefEq (a b : Expr) : TranslateEnvT Bool := do
  if a.hasFVar || b.hasFVar || a.hasMVar || b.hasMVar || a.hasLevelMVar || b.hasLevelMVar then
    return false
  isDefEq a b

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

private def valueArgs (n : Nat) : Expr :=
  if n ≤ 1 then mkApp (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.One)
    (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV)
  else mkApp2 (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.More)
    (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV) (valueArgs (n - 1))
termination_by n

private def builtinValue (b : Name) (n : Nat) : Expr :=
  mkApp3 (mkConst ``CekValue.VBuiltin) (mkConst b)
    (mkApp (mkConst ``List.nil [.zero]) (mkConst ``CekValue)) (valueArgs n)

private def certifyBindings (env layout : Expr) (indices : Array Nat) :
    TranslateEnvT (Option Expr) := do
  let mut proofs : Array Expr := #[]
  for (i, b, n) in #[(indices[0]!, ``BuiltinFun.IfThenElse, 3),
      (indices[1]!, ``BuiltinFun.ChooseList, 3),
      (indices[2]!, ``BuiltinFun.HeadList, 1), (indices[3]!, ``BuiltinFun.TailList, 1)] do
    let some actual := listItem? env i | return none
    let expected := builtinValue b n
    unless ← closedDefEq actual expected do return none
    let someValue := mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``CekValue) expected
    proofs := proofs.push (← mkEqRefl someValue)
  return some (mkAppN (mkConst ``ScalarSearch.Bindings.mk) (#[env, layout] ++ proofs))

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

@[blaster (register := false)]
theorem prefix_rule (sem : BuiltinSemanticsVariant) (block : Prefix sem) (fuel : Nat) :
    runSteps sem (Prefix.start sem block) fuel =
      if fuel < block.cost then .BudgetExhausted else
        runSteps sem block.target (fuel - block.cost) := Prefix.run_eq sem block fuel

private def liveState (s : Expr) : Bool :=
  s.isAppOfArity ``State.Eval 3 || s.isAppOfArity ``State.Return 2

/-- Restrict reduction to administrative transitions. In particular, stop
    before invoking saturated builtins and before entering force/case loop
    bodies, so the pass neither computes cryptography nor unrolls a list. -/
private def administrativeState (s : Expr) : Bool := Id.run do
  if let some fields := args? s ``State.Eval 3 then
    let code := fields[2]!.consumeMData
    if code.isConstOf ``PlutusCore.UPLC.Term.Term.Error then return false
    if let some force := args? code ``Term.Force 1 then
      if force[0]!.isAppOfArity ``Term.Case 2 then return false
    return true
  if let some fields := args? s ``State.Return 2 then
    let some cell := args? fields[0]! ``List.cons 3 | return false
    let frame := cell[1]!
    let mut callee := fields[1]!
    if let some right := args? frame ``Frame.RightApplicationOfValue 1 then
      callee := right[0]!
    else if frame.isAppOfArity ``Frame.LeftApplicationToValue 1 || frame.isConstOf ``Frame.ForceFrame then
      pure ()
    else return true
    if let some builtin := args? callee ``CekValue.VBuiltin 3 then
      return builtin[2]!.isAppOfArity ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.More 2
    return callee.isAppOfArity ``CekValue.VLam 2 || callee.isAppOfArity ``CekValue.VDelay 2
  return false

private def administrativeStep? (sem state : Expr) : TranslateEnvT (Option Expr) := do
  unless administrativeState state do return none
  try
    let target := (← whnf (mkApp2 (mkConst ``step) sem state)).consumeMData
    if liveState target then return some target else return none
  catch _ => return none

initialize registerTraceClass `Optimize.cekPrefix

/-- Fuse a bounded deterministic block and carry its definitional certificate.
    Payloads and unused environments are never recursively normalized here.
    This also works with symbolic remaining fuel introduced by a loop summary. -/
@[blaster runSteps]
def optimizeAdministrativePrefix (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if args.size != 3 then return none
  let state := args[1]!.consumeMData
  if state.hasMVar || state.hasLevelMVar || !liveState state then return none
  let mut target := state
  let mut cost := 0
  let mut stopped := false
  let mut seen : Std.HashSet Expr := {}
  for _ in [:32] do
    if seen.contains target then return none
    seen := seen.insert target
    let some next ← administrativeStep? args[0]! target |
      stopped := true
      break
    target := next
    cost := cost + 1
  if !stopped || cost < 2 || target.hasMVar || target.hasLevelMVar then return none
  let proof ← mkEqRefl target
  let block := mkAppN (mkConst ``Prefix.mk)
    #[args[0]!, state, target, mkNatLit cost, proof, mkConst ``True.intro]
  let canonical := mkApp2 (mkConst ``Prefix.start) args[0]! block
  trace[Optimize.cekPrefix] "fused {cost} administrative transitions"
  blaster_opt_prefix_rule f #[args[0]!, canonical, args[2]!]

end PlutusCore.UPLC.Optimize
