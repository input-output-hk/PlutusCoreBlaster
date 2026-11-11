import Lean

namespace PlutusCore.UPLC.BlueprintEncoding.AssuranceSchema
open Lean

-- The supported CIP meta-schema is bundled: validation never trusts a fetched schema.
def schemaText : String := include_str "assurance.schema.json"

def field (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
def str (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
def arr (j : Json) (k : String) : Array Json := ((j.getObjValAs? (Array Json) k).toOption).getD #[]
def asciiName (s : String) (dots := false) : Bool :=
  !s.isEmpty && s.data.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_' || c == '-' || (dots && c == '.')))
private def hex (s : String) : Bool :=
  !s.isEmpty && s.data.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- Only patterns used by the bundled schema are supported; an unknown one fails closed. -/
private def matchesPattern (pattern s : String) : Bool :=
  if pattern == "^[A-Za-z0-9_-]+$" then asciiName s
  else if pattern == "^[A-Za-z0-9_.-]+$" then asciiName s true
  else if pattern == "^[0-9a-f]{56}$" then s.length == 56 && hex s
  else if pattern == "^([0-9a-f]{2})+$" then s.length % 2 == 0 && hex s
  else if pattern == "^[0-9]{4}-(0[1-9]|1[0-2])-(0[1-9]|[12][0-9]|3[01])$" then
    match s.splitOn "-" with
    | [y, m, d] => y.length == 4 && y.data.all Char.isDigit && m.length == 2 && d.length == 2 &&
        (m.toNat?.getD 0 ≥ 1 && m.toNat?.getD 99 ≤ 12) && (d.toNat?.getD 0 ≥ 1 && d.toNat?.getD 99 ≤ 31)
    | _ => false
  else if pattern == "^#/definitions/.+" then s.startsWith "#/definitions/" && s.length > 14
  else if pattern == "^/parameters/(0|[1-9][0-9]*)$" then
    let n := s.drop 12
    s.startsWith "/parameters/" && !n.isEmpty && n.data.all Char.isDigit && (n == "0" || !n.startsWith "0")
  else if pattern == "^([0-9a-fA-F]{2})*$" then
    s.length % 2 == 0 && s.data.all (fun c => c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f'))
  else false

def bundledSchemas : List String := [schemaText,
  include_str "assurance-v2.schema.json", include_str "checking-context.schema.json",
  include_str "interface.schema.json", include_str "value.schema.json", include_str "blueprint.schema.json"]

private def lookupSchema (uri : String) : Except String Json := do
  for txt in bundledSchemas do
    let j ← Json.parse txt
    if str j "$id" == some uri then return j
  throw s!"unsupported schema identifier {uri}"

private def reference (root : Json) (ref : String) : Except String (Json × Json) := do
  let parts := ref.splitOn "#"
  let base ← if parts.head! == "" then pure root else lookupSchema parts.head!
  let mut node := base
  let pointer := (parts.drop 1).headD ""
  unless pointer == "" || pointer.startsWith "/" do throw "unsupported JSON pointer"
  for key in (pointer.splitOn "/").drop 1 do
    node ← node.getObjVal? ((key.replace "~1" "/").replace "~0" "~")
  return (base, node)

/-- Interpreter for the keywords used in our pinned assurance meta-schema. -/
private partial def validate (root schema value : Json) (path : String) : Except String Unit := do
  if let some ref := str schema "$ref" then
    let (base, target) ← reference root ref
    validate base target value path
  if schema == .bool false then throw s!"{path}: forbidden value"
  if let some kind := str schema "type" then
    let ok := match kind, value with
      | "object", .obj _ | "array", .arr _ | "string", .str _ => true
      | "boolean", .bool _ => true
      | "integer", .num n => n.exponent == 0
      | _, _ => false
    unless ok do throw s!"{path}: expected {kind}"
  if let some expected := field schema "const" then
    unless value == expected do throw s!"{path}: unexpected value"
  if let some (.arr values) := field schema "enum" then
    unless values.contains value do throw s!"{path}: value is not in the allowed enumeration"
  if let .num n := value then
    if let some (.num minimum) := field schema "minimum" then
      unless n.toFloat ≥ minimum.toFloat do throw s!"{path}: below minimum"
  if let .str s := value then
    if let some p := str schema "pattern" then
      unless matchesPattern p s do throw s!"{path}: invalid format"
    if let some n := (schema.getObjValAs? Nat "minLength").toOption then
      if s.length < n then throw s!"{path}: string is too short"
  if let .arr values := value then
    if let some n := (schema.getObjValAs? Nat "minItems").toOption then
      if values.size < n then throw s!"{path}: array is too short"
    if field schema "uniqueItems" == some (.bool true) then
      for i in [:values.size] do
        for k in [i+1:values.size] do
          if values[i]! == values[k]! then throw s!"{path}: duplicate item"
    if let some item := field schema "items" then
      for i in [:values.size] do validate root item values[i]! s!"{path}[{i}]"
  if let .obj values := value then
    if let some n := (schema.getObjValAs? Nat "minProperties").toOption then
      unless values.toList.length >= n do throw s!"{path}: too few properties"
    for required in arr schema "required" do
      let key ← required.getStr?
      unless (field value key).isSome do throw s!"{path}: missing '{key}'"
    let props := field schema "properties"
    for (key, v) in values.toList do
      if let some ps := field schema "propertyNames" then validate root ps (.str key) path
      match props >>= (fun p => field p key) with
      | some ps => validate root ps v s!"{path}.{key}"
      | none => match field schema "additionalProperties" with
          | some (.bool false) => throw s!"{path}: unknown field '{key}'"
          | some ps => validate root ps v s!"{path}.{key}"
          | none => pure ()
  if let some (.arr alternatives) := field schema "anyOf" then
    unless alternatives.any (fun s => (validate root s value path).isOk) do
      throw s!"{path}: no allowed schema alternative matched"
  for clause in arr schema "allOf" do validate root clause value path
  if let some (.arr alternatives) := field schema "oneOf" then
    unless (alternatives.filter (fun s => (validate root s value path).isOk)).size == 1 do
      throw s!"{path}: expected exactly one schema alternative"
  if let some denied := field schema "not" then
    if (validate root denied value path).isOk then throw s!"{path}: forbidden combination"
  if let some condition := field schema "if" then
    if (validate root condition value path).isOk then
      if let some consequence := field schema "then" then validate root consequence value path
    else
      if let some consequence := field schema "else" then validate root consequence value path

/-- Validate every structural requirement before parsing the document model. -/
def validateDocument (value : Json) : Except String Unit := do
  let uri ← value.getObjValAs? String "$schema"
  let schema ← lookupSchema uri
  validate schema schema value "$"
end PlutusCore.UPLC.BlueprintEncoding.AssuranceSchema
