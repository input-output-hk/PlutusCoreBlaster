import Blaster.Counterexample
import PlutusCore.UPLC.BlueprintEncoding.CounterexampleObserve

namespace PlutusCore.UPLC.BlueprintEncoding.Counterexample
open Lean Meta

/-- Try zero for an integer omitted from the model. Only evaluation of the
    original proposition can confirm it. Keep the completion out of the SMT model. -/
private unsafe def replayInput (name : Name) (type : Expr) (model : Blaster.Counterexample.Model) :
    MetaM (Expr × Json) := do
  match (model.bindings.filter (·.name == name)).toList with
  | [binding] =>
    let some value := binding.value | throwError "model value could not be reconstructed: {name}"
    unless ← isDefEq (← inferType value) type do throwError "model type differs from original binder: {name}"
    return (value, ← binding.toJson)
  | [] =>
    unless ← isDefEq type (mkConst ``Int) do throwError "missing model assignment: {name}"
    let value := toExpr (0 : Int)
    let binding : Blaster.Counterexample.Binding := { id := name, name, type, raw := "0", value := some value }
    return (value, (← binding.toJson).setObjVal! "origin" (toJson "replay-completion"))
  | _ => throwError "original binder has no unique model assignment: {name}"

/-- Confirm a model on the original, closed proposition. -/
unsafe def replay (original : Expr) (model : Blaster.Counterexample.Model) (targets : Array Name := #[]) : MetaM Json := do
  try
    let mut proposition := original
    let mut used : List Name := []
    let mut inputs : Array Json := #[]
    repeat
      let .forallE name type body _ := proposition | break
      if ← isProp type then break
      if used.contains name then throwError "shadowed original binder: {name}"
      let (value, input) ← replayInput name type model
      proposition := body.instantiate1 value
      used := name :: used
      inputs := inputs.push input
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
    let (instantiated, calls) ← observe proposition targets
    let holds ← decideClosed instantiated
    return Json.mkObj [("status", toJson (if holds then "not-reproduced" else "confirmed")),
      ("propertyHolds", toJson holds), ("inputs", toJson inputs), ("execution", observation), ("calls", toJson calls),
      ("method", toJson "Evaluate the instantiated original Lean proposition over the imported compiled UPLC")]
  catch e =>
    if e.isInterrupt then throw e
    return Json.mkObj [("status", toJson "unavailable"),
    ("error", toJson (← e.toMessageData.toString))]

end PlutusCore.UPLC.BlueprintEncoding.Counterexample
