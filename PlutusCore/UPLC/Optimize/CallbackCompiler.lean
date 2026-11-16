import PlutusCore.UPLC.Optimize.CompiledFold
import Lean
import Lean.Util.CollectAxioms

namespace PlutusCore.UPLC.Optimize.CallbackCompiler
open Lean Elab Tactic Meta
initialize registerTraceClass `Optimize.callbackCompiler

private partial def discriminant? (e : Expr) : MetaM (Option FVarId) := do
  let e ← if e.hasLooseBVars then pure e else whnf e
  if let .const name _ := e.getAppFn then
    if let .recInfo info ← getConstInfo name then
      if let some d := e.getAppArgs[info.getMajorIdx]? then
        if d.isFVar then
          let t ← whnf (← inferType d)
          if t.isConstOf ``PlutusCore.Data.Data || t.isAppOfArity ``List 1 || t.isAppOfArity ``Prod 2 then
            return some d.fvarId!
  if let some m ← matchMatcherApp? e (alsoCasesOn := true) then
    for d in m.discrs do
      if d.hasLooseBVars then continue
      let d ← whnf d
      let v := match d with | .proj _ _ v => v | _ => d
      if v.isFVar then
        let t ← whnf (← inferType v)
        if t.isConstOf ``PlutusCore.Data.Data || t.isAppOfArity ``List 1 || t.isAppOfArity ``Prod 2 then
          return some v.fvarId!
  for child in (match e with
      | .app f a => #[f, a]
      | .lam _ t b _ | .forallE _ t b _ => #[t, b]
      | .letE _ t v b _ => #[t, v, b]
      | .mdata _ b | .proj _ _ b => #[b]
      | _ => #[]) do
    if let some v ← discriminant? child then return some v
  return none

elab "callback_cases" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← goal.getType
  let mut selected ← discriminant? type
  if selected.isNone then
    let used := (collectFVars {} type).fvarSet
    for v in (← getLCtx).getFVars.reverse do
      if used.contains v.fvarId! && (← whnf (← inferType v)).isAppOfArity ``Prod 2 then
        selected := some v.fvarId!
        break
  let some id := selected | throwError "no callback input discriminant"
  let gs ← goal.cases id
  replaceMainGoal (gs.toList.map (·.mvarId))

private partial def conditional? (e : Expr) : Option (Expr × Expr) := do
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let args := e.getAppArgs
    if !args[1]!.hasLooseBVars && !args[2]!.hasLooseBVars then
      return (args[1]!, args[2]!)
  for child in (match e with
      | .app f a => #[f, a]
      | .lam _ t b _ | .forallE _ t b _ => #[t, b]
      | .letE _ t v b _ => #[t, v, b]
      | .mdata _ b | .proj _ _ b => #[b]
      | _ => #[]) do
    if let some c := conditional? child then return c
  none

elab "callback_branch" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (condition, decision) := conditional? (← goal.getType) |
    throwError "no callback condition"
  let (yes, no) ← goal.byCasesDec condition decision
  replaceMainGoal [yes.mvarId, no.mvarId]

-- These are definitional reductions of the CEK/builtin model. Integer and
-- byte-string arithmetic remain scalar operations in the emitted function.
macro "callback_reduce" : tactic =>
  `(tactic| simp_all only [id, Callback.evaluateInteger, Callback.evaluate,
    Option.map_some, Option.map_none, Option.bind_some, Option.bind_none,
    Callback.integerPlan, Plan.map, Plan.shift, Plan.Correct,
    CompiledFold.env, CompiledFold.Kind.literal,
    CekMachine.Live, CekMachine.runStepsPreservingState,
    CekMachine.preserving_zero, CekMachine.step, CekMachine.step.folding,
    CekMachine.evalBuiltin, Builtins.expectedArgs, List.get?Internal,
    BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    BuiltinFunctions.List.headList, BuiltinFunctions.List.tailList,
    BuiltinFunctions.List.chooseList, BuiltinFunctions.Data.unIData,
    BuiltinFunctions.Data.unBData, BuiltinFunctions.Data.unConstrData,
    BuiltinFunctions.Data.unListData, BuiltinFunctions.Pair.fstPair,
    BuiltinFunctions.Pair.sndPair, BuiltinFunctions.Bool.ifThenElse,
    BuiltinFunctions.Integer.addInteger, BuiltinFunctions.Integer.subtractInteger,
    BuiltinFunctions.Integer.multiplyInteger, BuiltinFunctions.Integer.equalsInteger,
    BuiltinFunctions.Integer.lessThanInteger, BuiltinFunctions.Integer.lessThanEqualsInteger,
    BuiltinFunctions.ByteString.equalsByteString, BuiltinFunctions.Data.equalsData,
    PlutusCore.List.headList, PlutusCore.List.tailList,
    PlutusCore.Data.unIData, PlutusCore.Data.unBData, PlutusCore.Data.unConstrData,
    PlutusCore.Data.unListData, PlutusCore.Pair.fstPair, PlutusCore.Pair.sndPair,
    PlutusCore.Bool.ifThenElse])

macro "compile_callback" : tactic =>
  `(tactic| repeat' first | exact ⟨_, rfl⟩ | callback_reduce | callback_cases | callback_branch | split)

macro "certify_callback" : tactic =>
  `(tactic| repeat' first | exact ⟨by trivial, by rfl⟩ | rfl | callback_reduce | callback_cases | callback_branch | split)

private def synthesize (type : Expr) (tactic : Syntax) (initialCase : Option FVarId := none) : MetaM Expr := do
  let type ← instantiateMVars type
  if type.hasMVar then throwError "callback type has unresolved metavariables"
  -- Keep only the target's transitive dependencies. Besides preventing
  -- vacuous synthesis from ambient optimizer hypotheses, this avoids quadratic
  -- clearing of the optimizer's large local context.
  let context ← getLCtx
  let mut dependencies := collectFVars {} type
  for decl in context.getFVars.reverse do
    if dependencies.fvarSet.contains decl.fvarId! then
      let localDecl ← decl.fvarId!.getDecl
      dependencies := collectFVars dependencies localDecl.type
      if let some value := localDecl.value? then
        dependencies := collectFVars dependencies value
  let mut minimal : LocalContext := {}
  for decl in context do
    if dependencies.fvarSet.contains decl.fvarId then
      minimal := minimal.addDecl decl
  let goal ← mkFreshExprMVarAt minimal #[] type .syntheticOpaque
  trace[Optimize.callbackCompiler] m!"CB goal {goal.mvarId!.name}"
  let cleanGoal := goal.mvarId!
  let initialGoals : Array MVarId ← match initialCase with
    | none => pure #[cleanGoal]
    | some id => do
      let gs ← cleanGoal.cases id
      pure (gs.map (·.mvarId))
  let action : TermElabM Unit := do
    for initialGoal in initialGoals do
      let goals ← Tactic.run initialGoal (evalTactic tactic)
      unless goals.isEmpty do
        for g in goals.take 2 do g.withContext do trace[Optimize.callbackCompiler] m!"CB open: {← ppExpr (← g.getType)}"
        throwError "unsupported callback: certificate has open goals"
  let _ ← action.run { errToSorry := false }
  trace[Optimize.callbackCompiler] "CB instantiate"
  let value ← instantiateMVars goal
  if value.hasMVar || value.hasSorry then throwError "incomplete callback certificate"
  return value

private def checkedProof (proof : Expr) : MetaM Expr := do
  let vars := (← getLCtx).getFVars
  let value ← mkLambdaFVars vars proof (usedOnly := true)
  let type ← inferType value
  let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let name := Name.str (← mkFreshId) "compiledCallbackCorrect"
  withOptions (fun opts => opts.setBool `Elab.async false) do
    addDecl (.thmDecl { name, levelParams := levels, type, value })
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => #[``propext, ``Classical.choice, ``Quot.sound].contains n) do
    throwError "callback proof uses unexpected axioms: {axioms}"
  return proof

def checkRewrite (proof type : Expr) : MetaM Unit := do
  let vars := (← getLCtx).getFVars
  let annotated := Expr.letE `checkedFoldRewrite type proof (.bvar 0) false
  let value ← mkLambdaFVars vars annotated (usedOnly := true)
  let type ← inferType value
  let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let name := Name.str (← mkFreshId) "compiledFoldRewrite"
  withOptions (fun opts => opts.setBool `Elab.async false) do
    addDecl (.thmDecl { name, levelParams := levels, type, value })
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => #[``propext, ``Classical.choice, ``Quot.sound].contains n) do
    throwError "fold rewrite uses unexpected axioms: {axioms}"

/-- Candidate erasure only: correctness is established afterwards against
    the original callback. Remove subtype packaging and its proof motives. -/
private partial def dataOnly (e : Expr) : Expr :=
  if e.isAppOfArity ``Subtype 2 then dataOnly e.getAppArgs[0]!
  else if e.isAppOfArity ``Subtype.mk 4 then dataOnly e.getAppArgs[2]!
  else if e.isAppOfArity ``Subtype.val 3 then dataOnly e.getAppArgs[2]!
  else match e with
  | .proj ``Subtype 0 b => dataOnly b
  | .app f a => .app (dataOnly f) (dataOnly a)
  | .lam n t b i => .lam n (dataOnly t) (dataOnly b) i
  | .forallE n t b i => .forallE n (dataOnly t) (dataOnly b) i
  | .letE n t v b c => .letE n (dataOnly t) (dataOnly v) (dataOnly b) c
  | .mdata _ b => dataOnly b
  | .proj n i b => .proj n i (dataOnly b)
  | _ => e

private def literalNat? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  let e := if e.isAppOfArity ``OfNat.ofNat 3 then e.getAppArgs[1]! else e
  match e with
  | .lit (.natVal n) => some n
  | _ => none

private partial def captureSlots (code : Expr) (depth : Nat := 0) : List Nat :=
  if code.isAppOfArity ``Term.Term.Var 1 then
    match (literalNat? code.getAppArgs[0]!) with
    | some n => if n ≥ depth + 3 then [n - depth - 3] else []
    | none => []
  else if code.isAppOfArity ``Term.Term.Lam 1 then
    captureSlots code.getAppArgs[0]! (depth + 1)
  else match code with
    | .app f a => captureSlots f depth ++ captureSlots a depth
    | .mdata _ b => captureSlots b depth
    | _ => []

private partial def compactEnv (env : Expr) (keep : List Nat) (index : Nat := 0) : Expr :=
  if env.isAppOfArity ``List.cons 3 then
    let cells :=  env.getAppArgs
    let value := if keep.contains index then (cells[1]!) else
      mkApp (mkConst ``CekValue.CekValue.VCon) (mkConst ``Term.Const.Unit)
    mkAppN env.getAppFn #[cells[0]!, value, compactEnv cells[2]! keep (index + 1)]
  else env

private def candidateBindings (bindings callback : Expr) : Expr := Id.run do
  unless bindings.isAppOfArity ``CompiledFold.Bindings.mk 5 do return bindings
  let cells :=  bindings.getAppArgs
  let keep := captureSlots callback ++ (literalNat? cells[1]!).toList ++ (literalNat? cells[2]!).toList
  return mkAppN bindings.getAppFn #[compactEnv cells[0]! keep, cells[1]!, cells[2]!, cells[3]!, cells[4]!]

/-- Proof-producing compilation. The candidate evaluator is run on a singleton
    list, then the emitted plan is checked against the original CEK for EVERY
    tail and continuation. Tail-dependent callbacks therefore cannot pass.
    No syntactic callback catalogue, field name or scalar predicate is used. -/
private def compileCore (kind bindings callback sem : Expr) (limit : Nat := 96) : MetaM Expr := withTransparency .default do
  let itemType ← whnf (mkApp (mkConst ``CompiledFold.Kind.Item) kind)
  let intType := mkConst ``Int
  let planType := mkApp (mkConst ``Plan) intType
  let candidateEnv := candidateBindings bindings callback
  let planFn ← withLocalDeclD `acc intType fun acc =>
    withLocalDeclD `element itemType fun element => do
      let list ← mkListLit itemType [element]
      let boxed := mkApp (mkConst ``CekValue.CekValue.VCon)
        (mkApp (mkConst ``Term.Const.Integer) acc)
      let rho := mkAppN (mkConst ``CompiledFold.env) #[kind, candidateEnv, callback, boxed, list]
      let stack ← mkListLit (mkConst ``CekMachine.Frame) []
      let state := mkAppN (mkConst ``CekMachine.State.Eval) #[stack, rho, callback]
      let candidate := mkAppN (mkConst ``Callback.evaluateInteger) #[sem, mkNatLit limit, state]
      let pred ← withLocalDeclD `plan planType fun plan => do
        mkLambdaFVars #[plan] (← mkEq candidate (← mkAppM ``Option.some #[plan]))
      let subtype := mkApp2 (mkConst ``Subtype [levelOne]) planType pred
      let witness ← synthesize subtype (← `(tactic| compile_callback)) (some element.fvarId!)
      let data := mkProj ``Subtype 0 witness
      mkLambdaFVars #[acc, element] data
  let planFn := dataOnly planFn
  if planFn.getUsedConstants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.CekMachine" ||
      n.toString.startsWith "PlutusCore.UPLC.Optimize.Callback.evaluate") then
    throwError "callback did not compile to scalar code"
  for v in (collectFVars {} planFn).fvarIds do
    if ← isProp (← inferType (mkFVar v)) then
      throwError "compiled callback depends on an ambient proof"
  let _ ← inferType planFn
  let ctor := mkAppN (mkConst ``CompiledFold.CompiledCallback.mk)
    #[kind, bindings, callback, sem, planFn]
  let ctorType ← whnf (← inferType ctor)
  let proof ← synthesize ctorType.bindingDomain!
    (← `(tactic| intro acc element tail continuation; cases element <;> certify_callback))
  let proof ← checkedProof proof
  let compiled := mkApp ctor proof
  let _ ← inferType compiled
  return compiled

private partial def envSlot? (env : Expr) (index : Nat) : Option Expr := do
  if !env.isAppOfArity ``List.cons 3 then none else
    let cells := env.getAppArgs
    match index with
    | 0 => some cells[1]!
    | n + 1 => envSlot? cells[2]! n

/-- Conservative eligibility check: a leaf callback may use the current head,
    accumulator and captures, but cannot inspect the tail or invoke the fold's
    recursive closure. Correctness still comes from the subsequent CEK proof. -/
private partial def itemOnly (env code : Expr) (depth : Nat := 0) : Bool := Id.run do
  if code.isAppOfArity ``Term.Term.Var 1 then
    let some n := literalNat? code.getAppArgs[0]! | return false
    return n != depth + 1 && n != depth + 2
  if code.isAppOfArity ``Term.Term.Apply 2 then
    let parts := code.getAppArgs
    if parts[1]!.isAppOfArity ``Term.Term.Var 1 &&
        literalNat? parts[1]!.getAppArgs[0]! == some (depth + 1) then
      let head := parts[0]!
      if head.isAppOfArity ``Term.Term.Var 1 then
        let some n := literalNat? head.getAppArgs[0]! | return false
        if n < depth + 3 then return false
        let some value := envSlot? env (n - depth - 3) | return false
        return value.isAppOfArity ``CekValue.CekValue.VBuiltin 3 &&
          value.getAppArgs[0]!.isConstOf ``Term.BuiltinFun.HeadList
      return false
  if code.isAppOfArity ``Term.Term.Lam 1 then
    return itemOnly env code.getAppArgs[0]! (depth + 1)
  match code with
  | .app f arg => return itemOnly env f depth && itemOnly env arg depth
  | .mdata _ body => return itemOnly env body depth
  | _ => return true

/-- Prove the callback once with unused closure slots abstracted, then instantiate
    that proof at the original captures. This avoids traversing large context
    values while retaining a certificate for the exact original environment. -/
private partial def abstractUnused (env : Expr) (keep : List Nat) (index : Nat)
    (k : Expr → MetaM Expr) : MetaM Expr := do
  if env.isAppOfArity ``List.cons 3 then
    let cells := env.getAppArgs
    let rebuild := fun value => abstractUnused cells[2]! keep (index + 1) fun rest =>
      k (mkAppN env.getAppFn #[cells[0]!, value, rest])
    if keep.contains index then rebuild cells[1]!
    else withLocalDeclD (Name.mkSimple s!"unusedCapture{index}") cells[0]! fun slot => do
      let result ← rebuild slot
      let fn ← mkLambdaFVars #[slot] result
      return (mkApp fn cells[1]!).headBeta
  else k env

def compile (kind bindings callback sem : Expr) (limit : Nat := 96) : MetaM Expr := do
  if bindings.isAppOfArity ``CompiledFold.Bindings.mk 5 then
    let cells := bindings.getAppArgs
    unless itemOnly cells[0]! callback do
      throwError "callback is recursive or depends on the list tail"
    let keep := captureSlots callback ++ (literalNat? cells[1]!).toList ++
      (literalNat? cells[2]!).toList
    abstractUnused cells[0]! keep 0 fun env => do
      let genericBindings := mkAppN bindings.getAppFn
        #[env, cells[1]!, cells[2]!, cells[3]!, cells[4]!]
      compileCore kind genericBindings callback sem limit
  else compileCore kind bindings callback sem limit

end PlutusCore.UPLC.Optimize.CallbackCompiler
