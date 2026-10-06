import PlutusCore.UPLC.BlueprintEncoding.Basic

namespace PlutusCore.UPLC.BlueprintEncoding.Applied
open Lean
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.BlueprintEncoding.Internal

/-- Applied values are checked at elaboration time. Unsupported refinements fail
closed; they are never silently treated as satisfied. Recursive references have
already been validated by `parseFunctionWire`. -/
private partial def conforms (defs schema : Json) (value : Const) : Except String Bool := do
  let fields ← schema.getObj?
  for (key, _) in fields.toArray do
    unless ["$ref", "title", "description", "$comment", "dataType", "index", "fields",
            "items", "keys", "values", "left", "right", "oneOf", "anyOf"].contains key do
      throw s!"unsupported applied-value schema constraint '{key}'"
  if let some ref := getOptStr schema "$ref" then
    let key := ((ref.drop 14).replace "~1" "/").replace "~0" "~"
    return ← conforms defs (← defs.getObjVal? key) value
  for key in ["oneOf", "anyOf"] do
    if let .ok (.arr choices) := schema.getObjVal? key then
      let matched ← choices.mapM fun s => conforms defs s value
      let count := matched.toList.count true
      return if key == "oneOf" then count == 1 else count > 0
  let kind := (getOptStr schema "dataType").getD ""
  match kind, value with
  | "", .Data _ => return true
  | "integer", .Data (.I _) | "bytes", .Data (.B _)
  | "#integer", .Integer _ | "#bytes", .ByteString _ | "#string", .String _
  | "#unit", .Unit | "#boolean", .Bool _ => return true
  | "constructor", .Data (.Constr i values) =>
    unless (← schema.getObjValAs? Nat "index") == i do return false
    let fields ← schema.getObjValAs? (Array Json) "fields"
    unless fields.size == values.length do return false
    return (← (fields.toList.zip values).mapM fun (s, v) => conforms defs s (.Data v)).all id
  | "list", .Data (.List values) | "#list", .ConstDataList values =>
    let items ← schema.getObjVal? "items"
    return (← values.mapM fun v => conforms defs items (.Data v)).all id
  | "map", .Data (.Map values) =>
    let keys ← schema.getObjVal? "keys"
    let vals ← schema.getObjVal? "values"
    return (← values.mapM fun (k, v) => do
      return (← conforms defs keys (.Data k)) && (← conforms defs vals (.Data v))).all id
  | "#pair", .PairData (left, right) =>
    return (← conforms defs (← schema.getObjVal? "left") (.Data left)) &&
      (← conforms defs (← schema.getObjVal? "right") (.Data right))
  | _, _ => return false

/-- Require an actual closed constant, in precisely the declared Data/native
representation. Scott encodings are rejected by this profile. -/
def validateValue (defs schema : Json) (term : PlutusCore.UPLC.Term.Term) : Except String Unit := do
  discard <| parseFunctionWire schema defs
  let .Const value := term | throw "applied parameter must be a closed value in its declared encoding"
  unless (← conforms defs schema value) do throw "applied parameter does not match its value schema"

/-- Upstream's general decoder permits open terms. Parameter artifacts must
be closed; de Bruijn indices are relative to the current binder depth. -/
private partial def closed (depth : Nat) : PlutusCore.UPLC.Term.Term → Bool
  | .Var index => index < depth
  | .Lam body => closed (depth + 1) body
  | .Apply fn arg => closed depth fn && closed depth arg
  | .Delay body | .Force body => closed depth body
  | .Constr _ fields => fields.all (closed depth)
  | .Case body branches => closed depth body && branches.all (closed depth)
  | .Const _ | .Builtin _ | .Error => true

/-- A Flat term artifact has no program-version prefix and no trailing payload. -/
def decodeValue (version : Version) (bytes : ByteArray) : Except String PlutusCore.UPLC.Term.Term := do
  let raw := String.mk (bytes.toList.map (Char.ofNat ∘ UInt8.toNat))
  let some bits := FlatEncoding.Internal.bitSequenceFromByteString raw.data []
    | throw "invalid Flat parameter bytes"
  let some (rest, term) := FlatEncoding.Internal.decodeTerm version 0 bits
    | throw "invalid or open Flat parameter term"
  unless closed 0 term do throw "invalid or open Flat parameter term"
  unless FlatEncoding.Internal.unpad rest == some [] do throw "trailing or invalid Flat parameter padding"
  return term

end PlutusCore.UPLC.BlueprintEncoding.Applied
