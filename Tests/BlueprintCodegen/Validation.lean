import PlutusCore.UPLC.BlueprintEncoding.Assurance

open Lean Elab Command
open PlutusCore.UPLC.BlueprintEncoding
open PlutusCore.UPLC.BlueprintEncoding.Internal

namespace Tests.BlueprintCodegen.Validation

-- Raw numeric spellings must be checked before recognizing Bool/Unit shapes.
run_cmd do
  for bad in ["-1", "1.5", "2.0", "1e-1", "null", "true", "\"1\""] do
    let ctor := "{\"dataType\":\"constructor\",\"index\":" ++ bad ++ ",\"fields\":[]}"
    for schema in [ctor, "{\"anyOf\":[" ++ ctor ++ "]}",
                   "{\"oneOf\":[" ++ ctor ++ ",{\"dataType\":\"constructor\",\"index\":1,\"fields\":[]}]}" ] do
      let doc := "{\"preamble\":{\"title\":\"tags\",\"version\":\"1\",\"plutusVersion\":\"v3\"},\"validators\":[],\"definitions\":{\"Bad\":" ++ schema ++ "}}"
      match parseBlueprint doc with
      | .ok _ => throwError "accepted malformed constructor index {bad}"
      | .error e => unless (e.splitOn "constructor index").length > 1 do throwError "wrong error: {e}"
  for choices in ["anyOf", "oneOf"] do
    let doc := "{\"preamble\":{\"title\":\"tags\",\"version\":\"1\",\"plutusVersion\":\"v3\"},\"validators\":[],\"definitions\":{\"Bad\":{\"" ++ choices ++ "\":[{\"dataType\":\"constructor\",\"index\":0,\"fields\":[]},{\"dataType\":\"constructor\",\"index\":0,\"fields\":[]}]}}}"
    match parseBlueprint doc with
    | .ok _ => throwError "accepted duplicate constructor index"
    | .error e => unless (e.splitOn "duplicate constructor index").length > 1 do throwError "wrong error: {e}"

-- Legacy execution settings must respect the selected language too.
run_cmd do
  for version in ["v1", "v2", "v3"] do
    for sem in ["A", "B", "C", "D", "E"] do
      let doc := Json.mkObj [
        ("preamble", Json.mkObj [("title", toJson "semantics"), ("version", toJson "1"), ("plutusVersion", toJson version)]),
        ("validators", toJson [Json.mkObj [("title", toJson "test"),
          ("budget", Json.mkObj [("steps", toJson (100 : Nat)), ("semantics", toJson sem)])]])]
      let allowed := if version == "v3" then ["C", "E"].contains sem else ["A", "B", "D"].contains sem
      unless (parseBlueprint doc.compress).isOk == allowed do throwError "wrong semantics compatibility: {version}/{sem}"

run_cmd do
  for bad in [toJson (1 : Nat), Json.bool true, Json.mkObj []] do
    let doc := Json.mkObj [
      ("preamble", Json.mkObj [("title", toJson "semantics"), ("version", toJson "1"), ("plutusVersion", toJson "v2")]),
      ("validators", toJson [Json.mkObj [("title", toJson "test"),
        ("budget", Json.mkObj [("steps", toJson (100 : Nat)), ("semantics", bad)])]])]
    if (parseBlueprint doc.compress).isOk then throwError "accepted a non-string semantics variant"

-- Inspect actual imported wrappers: a step-only V1/V2 budget must not become E.
run_cmd do
  let original ← ofExcept (Json.parse (include_str "fixtures/applied.json"))
  let validators ← ofExcept (original.getObjValAs? (Array Json) "validators")
  for (version, expected) in [("v1", ``PlutusCore.Default.Internal.BuiltinSemanticsVariant.defaultFunSemanticsVariantD),
                              ("v2", ``PlutusCore.Default.Internal.BuiltinSemanticsVariant.defaultFunSemanticsVariantD),
                              ("v3", ``PlutusCore.Default.Internal.BuiltinSemanticsVariant.defaultFunSemanticsVariantE)] do
    let validator ← ofExcept (validators[0]!.getObj?)
    let validator := validator.erase "hash"
    let preamble ← ofExcept ((← ofExcept (original.getObjVal? "preamble")).getObj?)
    let doc := Json.mkObj [("preamble", .obj (preamble.insert "plutusVersion" (toJson version))),
      ("definitions", Json.mkObj []), ("validators", toJson [Json.obj validator])]
    let (handle, path) ← IO.FS.createTempFile
    try
      handle.putStr doc.compress
      handle.flush
      let ns := Name.mkStr `Tests.BlueprintCodegen.Validation version
      discard <| elabBlueprintImport ns path.toString
      let some (.defnInfo wrapper) := (← getEnv).find? (Name.mkStr ns "applied_data")
        | throwError "missing generated wrapper"
      unless wrapper.value.getUsedConstants.contains expected do
        throwError "wrong default semantics for {version}"
    finally IO.FS.removeFile path

end Tests.BlueprintCodegen.Validation
