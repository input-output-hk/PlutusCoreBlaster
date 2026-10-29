import Blaster.Counterexample
import PlutusCore.UPLC.BlueprintEncoding.Basic

namespace PlutusCore.UPLC.BlueprintEncoding.Counterexample
open Lean Meta

/-- Confirm a model on the original, closed proposition. Name matching is only
    accepted for unique binders of matching types; erased/shadowed/unsupported
    binders are reported, never assigned guessed values. -/
unsafe def replay (original : Expr) (model : Blaster.Counterexample.Model) : MetaM Json := do
  try
    let mut proposition := original
    let mut used : List Name := []
    let mut inputs : Array Json := #[]
    repeat
      let .forallE name type body _ := proposition | break
      if ← isProp type then break
      if used.contains name then throwError "shadowed original binder: {name}"
      let candidates := model.bindings.filter (·.name == name)
      unless candidates.size == 1 do throwError "original binder has no unique model assignment: {name}"
      let some binding := candidates[0]? | throwError "missing model assignment"
      let some value := binding.value | throwError "model value could not be reconstructed: {name}"
      unless ← isDefEq (← inferType value) type do throwError "model type differs from original binder: {name}"
      proposition := body.instantiate1 value
      used := name :: used
      inputs := inputs.push (← binding.toJson)
    if proposition.hasFVar || proposition.hasMVar then throwError "replay proposition is not closed"
    let mut observation := Json.null
    if let .const (.str parent short) _ := proposition.getAppFn then
      let args := proposition.getAppArgs
      if short.endsWith "_returns" && !args.isEmpty then
        let wrapper := Name.mkStr parent (short.dropRight 8)
        let call := mkAppN (mkConst wrapper) (args.extract 0 (args.size - 1))
        let state ← evalExpr CekMachine.State (mkConst ``CekMachine.State) call
        observation := Json.mkObj [("call", toJson (← ppExpr call).pretty),
          ("state", toJson (reprStr state))]
        if let .Halt (.VCon (.Bool actual)) := state then
          observation := Json.mkObj [("call", toJson (← ppExpr call).pretty),
            ("state", toJson "Halt"), ("actual", toJson actual),
            ("expected", toJson (← evalExpr Bool (mkConst ``Bool) args.back!))]
    let decision ← try mkDecide proposition catch e =>
      if e.isInterrupt then throw e
      mkDecide (← withTransparency .all (whnf proposition))
    let holds ← evalExpr Bool (mkConst ``Bool) decision
    return Json.mkObj [("status", toJson (if holds then "not-reproduced" else "confirmed")),
      ("propertyHolds", toJson holds), ("inputs", toJson inputs), ("execution", observation),
      ("method", toJson "Evaluate the instantiated original Lean proposition over the imported compiled UPLC")]
  catch e =>
    if e.isInterrupt then throw e
    return Json.mkObj [("status", toJson "unavailable"),
    ("error", toJson (← e.toMessageData.toString))]

end PlutusCore.UPLC.BlueprintEncoding.Counterexample
