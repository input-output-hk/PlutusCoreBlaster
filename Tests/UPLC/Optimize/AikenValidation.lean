import Blaster
import PlutusCore.UPLC.Optimize.Aiken.Extension
import Tests.UPLC.Optimize.AikenFixture
import Lean.Util.CollectAxioms

open Lean Elab Command Term Meta
open PlutusCore.Default
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Optimize.Aiken

namespace Tests.AikenValidation
set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Expanded source pattern, not a call to a fictional UPLC decoder. -/
def rawEntry (a0 a1 a2 a3 a4 a5 a6 a7 p q : CekValue) (tail : PlutusCore.UPLC.CekValue.Environment)
    (k : Stack) (xs : List Data) : PlutusCore.UPLC.CekMachine.State := (.Eval k (.VCon (.ConstDataList xs) :: .VLam (.Lam (.Force (.Case (.Constr 0 [(.Var 0), (.Delay (.Const (.ConstDataList []))), (.Delay (.Apply (.Lam (.Force (.Case (.Constr 0 [(.Apply (.Apply (.Builtin .EqualsInteger) (.Const (.Integer 28))) (.Apply (.Builtin .LengthOfByteString) (.Var 0))), (.Delay (.Apply (.Apply (.Var 15) (.Apply (.Builtin .BData) (.Var 0))) (.Apply (.Apply (.Var 2) (.Var 2)) (.Apply (.Var 17) (.Var 1))))), (.Delay .Error)]) [(.Var 11)]))) (.Apply (.Builtin .UnBData) (.Apply (.Var 15) (.Var 0)))))]) [(.Var 13)]))) (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: .VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]) :: p :: q :: .VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]) :: .VBuiltin .MkCons [] (ArgV ⊙ a[ArgV]) :: .VBuiltin .HeadList [] a[ArgV] :: .VBuiltin .TailList [] a[ArgV] :: tail) :: (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: .VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]) :: p :: q :: .VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]) :: .VBuiltin .MkCons [] (ArgV ⊙ a[ArgV]) :: .VBuiltin .HeadList [] a[ArgV] :: .VBuiltin .TailList [] a[ArgV] :: tail)) (.Force (.Case (.Constr 0 [(.Var 0), (.Delay (.Const (.ConstDataList []))), (.Delay (.Apply (.Lam (.Force (.Case (.Constr 0 [(.Apply (.Apply (.Builtin .EqualsInteger) (.Const (.Integer 28))) (.Apply (.Builtin .LengthOfByteString) (.Var 0))), (.Delay (.Apply (.Apply (.Var 15) (.Apply (.Builtin .BData) (.Var 0))) (.Apply (.Apply (.Var 2) (.Var 2)) (.Apply (.Var 17) (.Var 1))))), (.Delay .Error)]) [(.Var 11)]))) (.Apply (.Builtin .UnBData) (.Apply (.Var 15) (.Var 0)))))]) [(.Var 13)])))

def unitValue : CekValue := .VCon .Unit

def entry (xs : List Data) : PlutusCore.UPLC.CekMachine.State :=
  rawEntry unitValue unitValue unitValue unitValue unitValue unitValue unitValue unitValue
    unitValue unitValue [] [] xs

mutual
  def containsTerm (needle : PlutusCore.UPLC.Term.Term) (t : PlutusCore.UPLC.Term.Term) : Bool :=
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

/-- The summarized body really occurs in the complete compiler artifact. -/
example : (match Tests.AikenValidationFixture.script with
    | .Program _ body => containsTerm validationBody body) = true := by decide

/- Wrong code and wrong builtin captures must not activate the rule. -/
run_cmd do
  runTermElabM fun _ => do
    let e ← elabTermAndSynthesize (← `(entry ([] : List Data))) none
    let state ← whnf e
    let sem ← elabTermAndSynthesize (← `((default : BuiltinSemanticsVariant))) none
    let args := #[sem, state, mkNatLit 100]
    let (ok, _) ← (optimizeCompiledValidation (mkConst ``runSteps) args).run default
    unless ok.isSome do throwError "literal compiled entry was not recognized"
    let badCapture := state.replace fun e =>
      if e.isConstOf ``BuiltinFun.HeadList then some (mkConst ``BuiltinFun.TailList) else none
    let (bad, _) ← (optimizeCompiledValidation (mkConst ``runSteps) (args.set! 1 badCapture)).run default
    unless bad.isNone do throwError "rule accepted a wrong builtin capture"
    let fields := state.getAppArgs
    let badBody := mkApp3 (mkConst ``PlutusCore.UPLC.CekMachine.State.Eval)
      fields[0]! fields[1]! (mkConst ``PlutusCore.UPLC.Term.Term.Error)
    let (bad, _) ← (optimizeCompiledValidation (mkConst ``runSteps) (args.set! 1 badBody)).run default
    unless bad.isNone do throwError "rule accepted a different UPLC body"
    logInfo "recognizer guards: accepted compiled body, rejected wrong capture/body"

run_cmd do
  for name in #[``validation_run_summary, ``compiled_validation_rule] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unexpected axiom in {name}: {ax}"
    logInfo m!"kernel proof audit {name}: {axioms}"

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

elab "#check_validation_optimization " budget:num : command => do
  runTermElabM fun _ => do
    let e ← elabTerm (← `(fun (xs : List Data) => runSteps default (entry xs) $budget)) none
    let (out, _) ← (Blaster.Optimize.Optimize.main e).run default
    unless out.getUsedConstants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.traversalPlan" || n.toString.startsWith "PlutusCore.UPLC.Optimize.Aiken.ValidationPlan" || n == ``validationSummary || n == ``validationPlan) do
      throwError "compiled validation rule did not leave a compact plan"
    unless distinctNodes out < 1000 do
      throwError "validation residual unexpectedly large: {distinctNodes out}"
    logInfo m!"validation fuel {budget.getNat}: {distinctNodes out} distinct residual nodes"

#check_validation_optimization 1000
#check_validation_optimization 10000
#check_validation_optimization 100000

/-- Concrete replay of the deliberately false SMT claim below. -/
example : runSteps default (entry [.I 0]) 100 = .Error := by rfl

#blaster (timeout: 10) (solve-result: 1) [∀ (n : Int),
  runSteps default (entry [.I n]) 100 = .Error → n < 0]

end Tests.AikenValidation
