import Blaster
import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.Optimize.Extension
import Tests.UPLC.Optimize.AikenFixture
import Tests.UPLC.Optimize.GenericFixture
import Lean.Util.CollectAxioms

open Lean Elab Command Term Meta
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations
open PlutusCore.UPLC.Optimize
open PlutusCore.UPLC.Optimize.ScalarSearch
open PlutusCore.Data (Data)

namespace Tests.GenericOptimization
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def unit : CekValue := .VCon .Unit

def compact : Bindings where
  env := [.VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]),
    .VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]),
    .VBuiltin .HeadList [] a[ArgV], .VBuiltin .TailList [] a[ArgV]]
  layout := ⟨0, 1, 2, 3⟩
  ifBound := rfl
  chooseBound := rfl
  headBound := rfl
  tailBound := rfl

/-- Different ordering, arbitrary unused value, and an opaque trailing context. -/
def permuted (unused : CekValue) (tail : PlutusCore.UPLC.CekValue.Environment) : Bindings where
  env := [.VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]),
    .VBuiltin .TailList [] a[ArgV], unused,
    .VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]), .VBuiltin .HeadList [] a[ArgV]] ++ tail
  layout := ⟨3, 0, 4, 1⟩
  ifBound := rfl
  chooseBound := rfl
  headBound := rfl
  tailBound := rfl

def identityK : Stack := [.RightApplicationOfValue (.VLam (.Var 0) [])]
def constantK : Stack := [.RightApplicationOfValue (.VLam (.Const .Unit) [])]

def compactBytes : ByteTraversal.Bindings where
  base := {
    env := [.VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]),
      .VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]), .VBuiltin .HeadList [] a[ArgV],
      .VBuiltin .TailList [] a[ArgV], .VBuiltin .MkCons [] (ArgV ⊙ a[ArgV])]
    layout := ⟨0, 1, 2, 3⟩
    ifBound := rfl, chooseBound := rfl, headBound := rfl, tailBound := rfl }
  consIndex := 4
  consBound := rfl

def permutedBytes (unused : CekValue) (tail : PlutusCore.UPLC.CekValue.Environment) :
    ByteTraversal.Bindings where
  base := {
    env := [.VBuiltin .MkCons [] (ArgV ⊙ a[ArgV]), .VBuiltin .TailList [] a[ArgV], unused,
      .VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]),
      .VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]), .VBuiltin .HeadList [] a[ArgV]] ++ tail
    layout := ⟨3, 4, 5, 1⟩
    ifBound := rfl, chooseBound := rfl, headBound := rfl, tailBound := rfl }
  consIndex := 0
  consBound := rfl

example : runSteps default (ByteTraversal.entry ⟨.eq, 3⟩ compactBytes [] [.B ⟨"abc"⟩]) 98 =
    .Halt (.VCon (.ConstDataList [.B ⟨"abc"⟩])) := by rfl
example : runSteps default
    (ByteTraversal.entry ⟨.eq, 3⟩ compactBytes [] [.B ⟨"abc"⟩, .List []]) 106 =
    .BudgetExhausted := by rfl
example : runSteps default
    (ByteTraversal.entry ⟨.eq, 3⟩ compactBytes [] [.B ⟨"abc"⟩, .List []]) 107 = .Error := by rfl
example : runSteps default (ByteTraversal.entry ⟨.lt, 3⟩ compactBytes [] [.B ⟨"abc"⟩]) 56 =
    .Error := by rfl

-- Complete-program execution checks include builtin initialization and result consumers.
example : cekExecuteProgram GenericOptimizationFixture.integerMember.script
    (GenericOptimizationFixture.params [.I 7]) 200 = .Halt (.VCon (.Bool true)) := by rfl
example : cekExecuteProgram GenericOptimizationFixture.integerThreshold.script
    (GenericOptimizationFixture.params [.I 4]) 200 = .Halt (.VCon .Unit) := by rfl
example : cekExecuteProgram GenericOptimizationFixture.integerThreshold.script
    (GenericOptimizationFixture.params [.I 12]) 200 = .Error := by rfl

-- First match ignores a malformed tail; a malformed element before a match fails.
example : runSteps default (entry (.integer .eq 7) compact [] [.I 7, .List []]) 48 =
    .Halt (.VCon (.Bool true)) := by rfl
example : runSteps default (entry (.integer .eq 7) compact [] [.I 6, .List []]) 91 =
    .Error := by rfl
example : runSteps default (entry (.integer .eq 7) compact [] [.List []]) 30 =
    .BudgetExhausted := by rfl
example : runSteps default (entry (.integer .eq 7) compact [] [.List []]) 31 =
    .Error := by rfl
example : runSteps default (entry (.integer .eq 7) compact [] [.I 7]) 47 =
    .BudgetExhausted := by rfl
example : runSteps default (entry (.integer .eq 7) compact identityK [.I 7]) 50 =
    .Halt (.VCon (.Bool true)) := by rfl
example : runSteps default (entry (.integer .lt 10) (permuted unit []) constantK [.I 4]) 50 =
    .Halt (.VCon .Unit) := by rfl

/-- Composition preserves earlier errors and charges a continuation only on success. -/
example (p : Predicate) (xs : List Data) (fuel : Nat) :
    runSteps default (entry p compact constantK xs) fuel =
      Composition.finish
        ((certificate compact p default).plan xs |>.bind (fun _ => .done 2 (.VCon .Unit))) fuel := by
  rw [run_summary, summary, constantK, Composition.execute_constant, Composition.execute_empty]
  rfl

mutual
  def containsTerm (needle t : PlutusCore.UPLC.Term.Term) : Bool :=
    t == needle || match t with
    | .Lam b | .Delay b | .Force b => containsTerm needle b
    | .Apply f a => containsTerm needle f || containsTerm needle a
    | .Constr _ ts => containsTerms needle ts
    | .Case t ts => containsTerm needle t || containsTerms needle ts
    | _ => false
  def containsTerms (needle : PlutusCore.UPLC.Term.Term) : List PlutusCore.UPLC.Term.Term → Bool
    | [] => false
    | t :: ts => containsTerm needle t || containsTerms needle ts
end

/-- The skeleton also occurs literally in the independently compiled Aiken fixture. -/
example : (match Tests.AikenValidationFixture.script with
    | .Program _ code => containsTerm
      (body ⟨5, 8, 10, 11⟩
        ((.bytes .eq (Tests.AikenValidationFixture.bytes (List.replicate 28 17)) : Predicate).test 10)) code) =
    true := by decide

example : (match Tests.AikenValidationFixture.script with
    | .Program _ code => containsTerm
      (ByteTraversal.body ⟨8, 11, 13, 14⟩ 12
        ((⟨.eq, 28⟩ : ByteTraversal.Predicate).test)) code) = true := by decide

run_cmd do
  for name in #[``Plan.run_eq, ``Plan.correct_bind, ``Plan.execute_bind,
      ``Traversal.correct, ``Search.correct, ``ScalarSearch.run_summary,
      ``scalar_search_rule, ``Composition.execute_empty, ``Composition.execute_identity,
      ``Composition.execute_constant, ``Administrative.apply_lambda,
      ``Composition.execute_assert, ``Administrative.lookup_tail,
      ``Administrative.lookup_head, ``Administrative.force_delay,
      ``Administrative.return_lambda, ``Administrative.return_lambda_left,
      ``Administrative.return_empty, ``ByteTraversal.run_summary, ``byte_traversal_rule,
      ``execute_traversal, ``Prefix.run_eq, ``prefix_rule, ``Composition.conditional_tail] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unexpected axiom in {name}: {ax}"
  logInfo "generic proof audit: no sorryAx or blasterProven"

private def literalState (stx : Syntax) : TermElabM Expr := do
  let e ← elabTermAndSynthesize stx none
  reduce e

run_cmd do
  runTermElabM fun _ => do
    let sem ← elabTermAndSynthesize (← `((default : BuiltinSemanticsVariant))) none
    let predicates ← pure #[← `((.integer .eq 7 : Predicate)), ← `((.integer .lt 10 : Predicate)),
      ← `((.integer .le (-3) : Predicate)),
      ← `((.bytes .eq ⟨"abc"⟩ : Predicate)), ← `((.bytes .lt ⟨"def"⟩ : Predicate)),
      ← `((.bytes .le ⟨"ghi"⟩ : Predicate))]
    for pred in predicates do
      for binding in #[← `(compact), ← `(permuted unit [])] do
        let state ← literalState (← `(entry $pred $binding [] ([] : List Data)))
        let args := #[sem, state, mkNatLit 1000]
        let (ok, _) ← (optimizeScalarSearch (mkConst ``runSteps) args).run default
        unless ok.isSome do throwError "generic scalar search was not recognized: {pred}, {binding}"
        let badCapture := state.replace fun e =>
          if e.isConstOf ``BuiltinFun.HeadList then some (mkConst ``BuiltinFun.TailList) else none
        let (bad, _) ← (optimizeScalarSearch (mkConst ``runSteps) (args.set! 1 badCapture)).run default
        unless bad.isNone do throwError "search rule accepted a wrong builtin binding"
        let badDecoder := state.replace fun e =>
          if e.isConstOf ``BuiltinFun.UnIData then some (mkConst ``BuiltinFun.UnBData)
          else if e.isConstOf ``BuiltinFun.UnBData then some (mkConst ``BuiltinFun.UnIData) else none
        let (bad, _) ← (optimizeScalarSearch (mkConst ``runSteps) (args.set! 1 badDecoder)).run default
        unless bad.isNone do throwError "search rule accepted a mismatched decoder"
        let badRecursion := state.replace fun e =>
          if e.isAppOfArity ``PlutusCore.UPLC.Term.Term.Apply 2 then
            let call := e.getAppArgs
            if call[0]!.isAppOfArity ``PlutusCore.UPLC.Term.Term.Var 1 &&
                Expr.eqv call[0]! call[1]! then
              some (mkApp2 (mkConst ``PlutusCore.UPLC.Term.Term.Apply) call[0]!
                (mkApp (mkConst ``PlutusCore.UPLC.Term.Term.Var) (mkNatLit 0)))
            else none
          else none
        unless badRecursion != state do throwError "negative recursion fixture did not change"
        let (bad, _) ← (optimizeScalarSearch (mkConst ``runSteps) (args.set! 1 badRecursion)).run default
        unless bad.isNone do throwError "search rule accepted a different recursive call"
    logInfo "recognition: six predicates, two layouts; wrong bindings/decoders rejected"

partial def distinctNodes (root : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    unless seen.contains e do
      seen := seen.insert e
      match e with
      | .app f a => todo := f :: a :: todo
      | .lam _ t b _ | .forallE _ t b _ => todo := t :: b :: todo
      | .letE _ t v b _ => todo := t :: v :: b :: todo
      | .mdata _ b | .proj _ _ b => todo := b :: todo
      | _ => pure ()
  return seen.size

run_cmd do
  runTermElabM fun _ => do
    for pred in #[← `((.integer .eq 7 : Predicate)), ← `((.integer .lt 10 : Predicate)),
        ← `((.bytes .eq ⟨"abc"⟩ : Predicate))] do
      for stack in #[← `(([] : Stack)), ← `(identityK), ← `(constantK)] do
        let mut counts : Array Nat := #[]
        for budget in #[1000, 10000, 100000] do
          let fuel := Syntax.mkNumLit (toString budget)
          let e ← elabTermAndSynthesize (← `(fun (unused : CekValue) (tail : PlutusCore.UPLC.CekValue.Environment)
              (xs : List Data) => runSteps default (entry $pred (permuted unused tail) $stack xs) $fuel)) none
          let (out, _) ← (Blaster.Optimize.Optimize.main e).run default
          lambdaTelescope out fun parameters result => do
            unless parameters.size == 3 do throwError "unexpected residual function arity"
            if result.containsFVar parameters[0]!.fvarId! ||
                result.containsFVar parameters[1]!.fvarId! then
              throwError "unused capture or trailing context survived the summary"
          unless out.getUsedConstants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.searchPlan") do
            throwError "generic search did not leave its compact recursive plan"
          let count := distinctNodes out
          unless count < 1000 do throwError "generic residual grew to {count} nodes"
          counts := counts.push count
        unless counts.all (· == counts[0]!) do throwError "fuel-dependent expansion: {counts}"
        logInfo m!"generic residual {pred}, {stack}: {counts} nodes"

run_cmd do
  runTermElabM fun _ => do
    let sem ← elabTermAndSynthesize (← `((default : BuiltinSemanticsVariant))) none
    for pred in #[← `((⟨.eq, 28⟩ : ByteTraversal.Predicate)),
        ← `((⟨.eq, 32⟩ : ByteTraversal.Predicate)), ← `((⟨.lt, 8⟩ : ByteTraversal.Predicate)),
        ← `((⟨.le, 64⟩ : ByteTraversal.Predicate))] do
      for bindings in #[← `(compactBytes), ← `(permutedBytes unit [])] do
        let state ← literalState (← `(ByteTraversal.entry $pred $bindings [] ([] : List Data)))
        let args := #[sem, state, mkNatLit 1000]
        let (ok, _) ← (optimizeByteTraversal (mkConst ``runSteps) args).run default
        unless ok.isSome do throwError "generic byte traversal was not recognized"
        let badCapture := state.replace fun e =>
          if e.isConstOf ``BuiltinFun.MkCons then some (mkConst ``BuiltinFun.HeadList) else none
        let (bad, _) ← (optimizeByteTraversal (mkConst ``runSteps) (args.set! 1 badCapture)).run default
        unless bad.isNone do throwError "byte traversal accepted a wrong reconstruction builtin"
      let mut counts : Array Nat := #[]
      for budget in #[1000, 10000, 100000] do
        let fuel := Syntax.mkNumLit (toString budget)
        let e ← elabTermAndSynthesize (← `(fun (unused : CekValue)
            (tail : PlutusCore.UPLC.CekValue.Environment) (xs : List Data) =>
            runSteps default (ByteTraversal.entry $pred (permutedBytes unused tail) [] xs) $fuel)) none
        let (out, _) ← (Blaster.Optimize.Optimize.main e).run default
        lambdaTelescope out fun parameters result => do
          if result.containsFVar parameters[0]!.fvarId! || result.containsFVar parameters[1]!.fvarId! then
            throwError "unused byte-traversal captures survived the summary"
        unless out.getUsedConstants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.traversalPlan") do
          throwError "byte traversal did not leave its compact recursive plan"
        counts := counts.push (distinctNodes out)
      unless counts.all (· == counts[0]!) && counts[0]! < 1000 do
        throwError "byte traversal expanded with fuel: {counts}"
      logInfo m!"generic byte traversal {pred}: {counts} nodes"

-- Full preparation must remove the CEK runner as well as bound the root expression.
#prep_uplc genericInteger GenericOptimizationFixture.integerMember GenericOptimizationFixture.params 100000
#prep_uplc genericBytes GenericOptimizationFixture.bytesMember GenericOptimizationFixture.params 100000
#prep_uplc genericThreshold GenericOptimizationFixture.integerThreshold GenericOptimizationFixture.params 100000

def eagerScript : PlutusCore.UPLC.PlutusScript.PlutusScript :=
  ⟨.PlutusV3, Tests.AikenValidationFixture.script⟩
#prep_uplc genericEager eagerScript Tests.AikenValidationFixture.params 100000

run_cmd do
  for name in #[``genericInteger.prop, ``genericBytes.prop, ``genericThreshold.prop, ``genericEager.prop] do
    let ci ← getConstInfo name
    let e := ci.value!
    let used := e.getUsedConstants
    if used.contains ``runSteps || used.contains ``runStepsPreservingState || used.contains ``step then
      throwError "general CEK evaluator survived full preparation of {name}: {used}"
    if name == ``genericEager.prop then
      unless used.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.searchPlan") &&
          used.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.traversalPlan") do
        throwError "full eager preparation did not retain both generic summaries"
    unless distinctNodes e < 1000 do throwError "full preparation expanded: {name}"
    logInfo m!"full preparation {name}: {distinctNodes e} nodes; no CEK runner"

-- A false claim still produces a concrete model, independently replayed below.
example : runSteps default (entry (.integer .eq 7) compact [] [.I 7]) 100 =
    .Halt (.VCon (.Bool true)) := by rfl
#blaster (timeout: 10) (solve-result: 1) [∀ (n : Int),
  runSteps default (entry (.integer .eq 7) compact [] [.I n]) 100 =
    .Halt (.VCon (.Bool true)) → n < 0]

-- Counterexamples also survive *full-program* preparation, including Cardano decoding.
#blaster (timeout: 10) (solve-result: 1) [∀ (n : Int),
  genericInteger.prop [.I n] = .Halt (.VCon (.Bool true)) → n < 0]

example : genericEager.exec
    [.B (Tests.AikenValidationFixture.bytes (List.replicate 28 17))] = .Halt (.VCon .Unit) := by rfl
#blaster (timeout: 10) (solve-result: 1) [∀ (b : PlutusCore.ByteString.ByteString),
  genericEager.prop [.B b] ≠ .Halt (.VCon .Unit)]

end Tests.GenericOptimization
