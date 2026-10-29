import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.BlueprintEncoding.CounterexampleData

namespace PlutusCore.UPLC.BlueprintEncoding.Counterexample
open Lean Meta
open Blaster.Counterexample

/-- Follow specification definitions, without opening imported library internals. -/
private partial def usesTarget (e : Expr) (targets : Array Name) (seen : List Name := []) : MetaM Bool := do
  for name in e.getUsedConstants do
    if targets.contains name then return true
    if !seen.contains name && !(← getEnv).isImportedConst name then
      if let some (.defnInfo info) := (← getEnv).find? name then
        if ← usesTarget info.value targets (name :: seen) then return true
  return false

private def unfoldOne? (e : Expr) : MetaM (Option Expr) := do
  let .const name levels := e.getAppFn | return none
  if (← getEnv).isImportedConst name then return none
  let some (.defnInfo info) := (← getEnv).find? name | return none
  return some ((mkAppN (info.value.instantiateLevelParams info.levelParams levels) e.getAppArgs).headBeta)

private unsafe def exportExpr (name : Name) (e : Expr) : MetaM Json := do
  let type ← inferType e
  let b : Binding := { id := name, name, type, raw := (← ppExpr e).pretty, value := some e }
  b.toJson

/-- Only arguments with an installed codec are source-level observations. -/
private unsafe def sourceArguments (e : Expr) : MetaM (Array Json) := do
  let mut type ← inferType e.getAppFn
  let mut result := #[]
  for arg in e.getAppArgs do
    let .forallE name _ body _ ← whnf type | break
    let argType ← inferType arg
    if !arg.hasLooseBVars && !arg.hasFVar && !arg.hasMVar then
      if let .some _ ← trySynthInstance (← mkAppM ``ToCEX #[argType]) then
        let value ← exportExpr name arg
        result := result.push (Json.mkObj [("function", toJson (e.getAppFn.constName?.getD .anonymous).toString),
          ("argument", value)])
    type := body.instantiate1 arg
  return result

private def quoteTerminal (state : CekMachine.State) : MetaM Expr := do
  match state with
  | .Error => return mkConst ``CekMachine.State.Error
  | .Halt (.VCon c) =>
    return mkApp (mkConst ``CekMachine.State.Halt)
      (mkApp (mkConst ``CekValue.CekValue.VCon) (toExpr c))
  | _ => throwError "CEK replay is unfinished or returns a non-constant value"

private structure Observations where
  cache : Std.HashMap Expr Expr := {}
  calls : Array Json := #[]

/-- Evaluate only digest-checked imported wrapper calls. Keep their exact terminal
    states in the proposition, preserving all return values. Follow helper calls
    one definition at a time so source contexts survive their Data encoding. -/
private unsafe def visit (e : Expr) (targets : Array Name)
    (parents : Array Json) (fuel : Nat) : StateT Observations MetaM Expr := do
  let fuel + 1 := fuel | throwError "counterexample call discovery depth exceeded"
  if let some cached := (← get).cache[e]? then return cached
  if e.hasLooseBVars || !(← usesTarget e targets) then return e
  let type ← inferType e
  let state := (← whnf type).isConstOf ``CekMachine.State
  let result ← if state && targets.contains (e.getAppFn.constName?.getD .anonymous) then do
    let actual ← evalExpr CekMachine.State (mkConst ``CekMachine.State) e
    let quoted ← quoteTerminal actual
    let mut arguments := #[]
    let mut sources := parents
    for h : i in [:e.getAppArgs.size] do
      let arg := e.getAppArgs[i]
      arguments := arguments.push (← exportExpr (Name.mkSimple s!"a{i}") arg)
      -- A direct encoder application can carry the typed source value even
      -- when there is no intermediate State-producing adapter.
      if arg.isApp && arg.getAppFn.isConst then
        sources := sources ++ (← sourceArguments arg)
    let outcome := match actual with | .Halt _ => "halted" | .Error => "rejected" | _ => "unfinished"
    let call := (← ppExpr e).pretty
    modify fun s => { s with calls := s.calls.push (Json.mkObj [
      ("target", toJson (e.getAppFn.constName?.getD .anonymous).toString), ("call", toJson call),
      ("outcome", toJson outcome), ("arguments", toJson arguments),
      ("sourceArguments", toJson sources)]) }
    pure quoted
  else if state || (← isProp e) then do
    if let some opened ← unfoldOne? e then
      let parents ← if state then pure (parents ++ (← sourceArguments e)) else pure parents
      visit opened targets parents fuel
    else
      let mut result := e.getAppFn
      for arg in e.getAppArgs do
        result := mkApp result (← visit arg targets parents fuel)
      pure result
  else pure e
  modify fun s => { s with cache := s.cache.insert e result }
  return result

unsafe def observe (original : Expr) (targets : Array Name) : MetaM (Expr × Array Json) := do
  if targets.isEmpty then return (original, #[])
  let (result, observations) ← visit original targets #[] 64 |>.run {}
  unless !observations.calls.isEmpty do throwError "no scoped compiled call could be replayed"
  return (result, observations.calls)

/-- Decide closed logical structure without unfolding native arithmetic decision
    procedures into predicates that no longer have a Decidable instance. -/
unsafe def decideClosed (p : Expr) (fuel : Nat := 64) : MetaM Bool := do
  let fuel + 1 := fuel | throwError "counterexample proposition replay depth exceeded"
  try
    return ← evalExpr Bool (mkConst ``Bool) (← mkDecide p)
  catch e => if e.isInterrupt then throw e
  let args := p.getAppArgs
  match (p.getAppFn.constName?.getD .anonymous), args.toList with
  | ``And, [a, b] => return (← decideClosed a fuel) && (← decideClosed b fuel)
  | ``Or, [a, b] => return (← decideClosed a fuel) || (← decideClosed b fuel)
  | ``Iff, [a, b] => return (← decideClosed a fuel) == (← decideClosed b fuel)
  | ``Not, [a] => return !(← decideClosed a fuel)
  | _, _ =>
    if let .forallE _ premise body _ := p then
      if !(← isProp premise) || body.hasLooseBVars then throwError "dependent proposition cannot be replayed"
      return !(← decideClosed premise fuel) || (← decideClosed body fuel)
    let reduced ← withTransparency .all (whnf p)
    if reduced == p then throwError "closed proposition has no executable decision procedure"
    decideClosed reduced fuel

end PlutusCore.UPLC.BlueprintEncoding.Counterexample
