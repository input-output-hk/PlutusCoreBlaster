import PlutusCore.UPLC.BlueprintEncoding.Assurance
open Lean Elab Command
open PlutusCore.UPLC.BlueprintEncoding
open PlutusCore.UPLC.BlueprintEncoding.Internal

run_cmd do
  let tree := "{\"anyOf\":[{\"dataType\":\"constructor\",\"index\":0,\"fields\":[{\"dataType\":\"integer\"}]},{\"dataType\":\"constructor\",\"index\":1,\"fields\":[{\"$ref\":\"#/definitions/Tree\"},{\"$ref\":\"#/definitions/Tree\"}]}]}"
  let treeJson ← ofExcept (Json.parse tree)
  let ref := Json.mkObj [("$ref", toJson "#/definitions/Tree")]
  let defs := Json.mkObj [("Tree", treeJson)]
  let wire ← ofExcept (parseFunctionWire ref defs)
  unless wire.encoding == .asData && (match wire.ptype with | .data => true | _ => false) do throwError "recursive Data boundary narrowed"
  let nativeList := Json.mkObj [("dataType", toJson "#list"), ("items", ref)]
  let listWire ← ofExcept (parseFunctionWire nativeList defs)
  unless listWire.encoding == .asNative "#list" && (match listWire.ptype with | .list .data => true | _ => false) do
    throwError "native container lost its representation around a recursive Data element"
  for (name, json) in [
      ("alias", "{\"Tree\":{\"$ref\":\"#/definitions/Tree\"}}"),
      ("indirect alias", "{\"Tree\":{\"$ref\":\"#/definitions/Other\"},\"Other\":{\"$ref\":\"#/definitions/Tree\"}}"),
      ("missing", "{}"),
      ("native recursion", "{\"Tree\":{\"dataType\":\"#list\",\"items\":{\"$ref\":\"#/definitions/Tree\"}}}")] do
    let ds ← ofExcept (Json.parse json)
    match parseFunctionWire ref ds with
    | .error _ => pure ()
    | .ok _ => throwError "accepted invalid {name}"
  let mutualDefs ← ofExcept (Json.parse "{\"Tree\":{\"anyOf\":[{\"dataType\":\"constructor\",\"index\":0,\"fields\":[]},{\"dataType\":\"constructor\",\"index\":1,\"fields\":[{\"$ref\":\"#/definitions/Other\"}]}]},\"Other\":{\"dataType\":\"list\",\"items\":{\"$ref\":\"#/definitions/Tree\"}}}")
  discard <| ofExcept (parseFunctionWire ref mutualDefs)
  logInfo "PASS recursive, mutually recursive, unresolved, alias-cycle and native-cycle schemas"
