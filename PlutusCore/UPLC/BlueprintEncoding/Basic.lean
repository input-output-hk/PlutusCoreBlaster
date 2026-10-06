import Lean
import Cryptograph.Blake2b
import PlutusCore.UPLC.BlueprintEncoding.Schema

import PlutusCore.IsData
import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.PlutusScript
import PlutusCore.UPLC.ScriptEncoding.Basic
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.BlueprintEncoding

open Lean Elab Command Term Meta
open PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.ScriptEncoding.Internal (singleCborEncodedScriptFromHex?)
open PlutusCore.IsData (IsData)

/-! ## CIP-57 Plutus Blueprint import

This module implements the `#import_blueprints` command, which reads a CIP-57
`plutus.json` blueprint file at compile time and emits Lean definitions for
each validator.

For each validator it produces:
- `<ns>.<title> : PlutusScript`
- `<ns>.<title>_hash : String`  (when hash present)
- `<ns>.<title>_paramCount : Nat`  (when unapplied params > 0)
- Lean `structure` or `inductive` for datum/redeemer/parameter schemas,
  together with `IsData` instances, when the schema can be expressed in terms
  of the built-in Plutus types.
- `<ns> : BlueprintInfo`  — human-readable summary of the whole blueprint.

### Coordinated compiled-interface dialect

The draft dialect carries ordered interface references and schema-defined parameter
representations. Importing it alone emits raw scripts. Assurance checking supplies
the selected purpose and execution settings separately, generating each property's
wrappers in an isolated environment. Runtime binders stay raw Data.

### Legacy applied-validator wrappers

CIP-57 splits a validator's inputs into `parameters` / `datum` / `redeemer` and
leaves the script context implicit, so it cannot say *what the compiled program
is actually applied to*. Two additional (legal, optional) validator fields close
that gap:

```json
"arguments": [ { "encoding": "asData", "schema": { "$ref": "…" } }, … ],
"budget":    { "steps": 2500 }
```

`arguments` is the ordered list of terms the program is applied to; `budget`
gives the CEK step count to run for. When both are present *and* usable, the
`PlutusScript` is emitted as `<ns>.<title>_script` and the plain
`<ns>.<title>` becomes a wrapper that encodes its Lean arguments and runs the
CEK machine, so properties can be stated as `<title> a₀ a₁ … : State`.

The rename is **conditional**: a validator without `arguments` (every Aiken
blueprint) keeps `<ns>.<title> : PlutusScript` unchanged, and so does a
validator whose `arguments`/`budget` cannot be honoured (see
`Internal.wrapperBlocker`). `_hash` and `_paramCount` always keep the plain
`<title>` prefix.
-/

/-! ### Public summary types -/

/-- A Plutus on-chain type parsed from a CIP-57 JSON Schema. -/
inductive PlutusType where
  | integer    : PlutusType
  | bytestring : PlutusType
  | string     : PlutusType
  | bool       : PlutusType
  | unit       : PlutusType
  | void       : PlutusType
  | data       : PlutusType
  | list       (items : PlutusType)                                               : PlutusType
  | map        (keys values : PlutusType)                                         : PlutusType
  | pair       (left right : PlutusType)                                          : PlutusType
  /-- A single constructor: optional name, 0-based index, field (name × type) pairs. -/
  | constr     (title : Option String) (index : Nat)
               (fields : List (Option String × PlutusType))                       : PlutusType
  /-- Sum type. -/
  | anyOf      (variants : List PlutusType)                                       : PlutusType
  /-- A reference to a named definition emitted as its own Lean type. -/
  | named      (name : String)                                                    : PlutusType
  | opaque     (name : String)                                                    : PlutusType
  deriving Repr, Inhabited

/-- A typed slot (datum, redeemer, or parameter) from a CIP-57 validator. -/
structure SchemaInfo where
  /-- Slot label, e.g. `"datum"`, `"_redeemer"`, `"multisigHash"`. -/
  title    : Option String
  /-- Lean-safe type name resolved from the `definitions` section (e.g. `"MultisigRedeemer"`). -/
  typeName : Option String
  /-- Fully-resolved Plutus type. -/
  ptype    : PlutusType
  deriving Repr, Inhabited

/-- How one applied argument is encoded before the compiled program is applied
    to it (the `encoding` field of a validator `arguments` entry). -/
inductive ArgEncoding where
  /-- The argument is passed as a `Data` constant — i.e. `IsData.toData`
      wrapped in `Term.Const (Const.Data …)`. -/
  | asData             : ArgEncoding
  | asNative (kind : String) : ArgEncoding
  /-- The argument is Scott-encoded. There is no Scott encoder in this package
      (nor in `CardanoLedgerApi`), so no wrapper is emitted for it. -/
  | asScott            : ArgEncoding
  /-- Any other `encoding` keyword; unknown to this importer. -/
  | other (name : String) : ArgEncoding
  deriving Repr, Inhabited, BEq

/-- One entry of a validator's `arguments` array: the encoding, plus the
    argument's Plutus type resolved through the blueprint `definitions`. -/
structure ArgumentInfo where
  encoding : ArgEncoding
  ptype    : PlutusType
  deriving Repr, Inhabited

/-- A validator's declared execution budget. CIP-57 does not define this field;
    the two shapes below are what the emitting pipelines produce. -/
inductive BudgetInfo where
  /-- A CEK step count — directly usable as `cekExecuteProgram`'s third argument. -/
  | steps   (n : Nat)          : BudgetInfo
  | semanticSteps (n : Nat) (semantics : String) : BudgetInfo
  /-- Ledger execution units. There is no conversion from these to a step
      count, so no wrapper is emitted for a validator budgeted this way. -/
  | exUnits (exCPU exMem : Nat) : BudgetInfo
  deriving Repr, Inhabited

/-- Metadata for one validator entry in a CIP-57 blueprint. -/
structure ValidatorInfo where
  title       : String
  /-- Optional stable identifier (recommended by the blueprint-assurance CIP
      so external documents can reference validators robustly). -/
  id          : Option String
  description : Option String
  hash        : Option String
  /-- The compiled Plutus script, if present in the blueprint. -/
  script      : Option PlutusScript
  datum       : Option SchemaInfo
  redeemer    : Option SchemaInfo
  parameters  : Array SchemaInfo
  deriving Repr, Inhabited

/-- Top-level summary of a CIP-57 blueprint file. -/
structure BlueprintInfo where
  title         : String
  description   : Option String
  version       : String
  plutusVersion : String
  license       : Option String
  validators    : Array ValidatorInfo
  deriving Repr

/-! ### Internal JSON parsing -/

namespace Internal

structure BlueprintPreamble where
  title         : String
  description   : Option String
  version       : String
  plutusVersion : String
  license       : Option String

structure BlueprintValidator where
  title        : String
  id           : Option String
  description  : Option String
  compiledCode : Option String
  hash         : Option String
  datum        : Option SchemaInfo
  redeemer     : Option SchemaInfo
  parameters   : Array SchemaInfo
  /-- The ordered list of terms the compiled program is applied to, when the
      blueprint declares it. `none` means the field is absent (the CIP-57
      baseline) — no applied-validator wrapper is emitted and the plain
      validator name stays bound to the `PlutusScript`. -/
  arguments    : Option (Array ArgumentInfo) := none
  /-- The declared execution budget, when present. -/
  budget       : Option BudgetInfo := none
  invocations  : Array (String × Array ArgumentInfo) := #[]

structure Blueprint where
  extended   : Bool := false
  preamble   : BlueprintPreamble
  validators : Array BlueprintValidator
  /-- Every nameable definition (record / enum / sum-of-products), as
      `(type name, parsed structure)`, for emitting standalone Lean types. -/
  namedTypes : List (String × PlutusType) := []

-- ---------------------------------------------------------------------------
-- JSON helpers
-- ---------------------------------------------------------------------------

def getStr (j : Lean.Json) (key : String) : Except String String :=
  match j.getObjVal? key with
  | .ok (.str s) => .ok s
  | .ok _        => .error s!"field '{key}' must be a string"
  | .error _     => .error s!"missing required field '{key}'"

def getOptStr (j : Lean.Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .ok (.str s) => .some s
  | _            => .none

/-- Decode JSON Pointer token escapes: `~1` → `/`, then `~0` → `~`. -/
private def decodeJsonPointer (s : String) : String :=
  String.intercalate "~" (String.intercalate "/" (s.splitOn "~1") |>.splitOn "~0")

-- ---------------------------------------------------------------------------
-- Schema / PlutusType parsing
-- ---------------------------------------------------------------------------

/-- The untitled two-variant, field-less sum that plutus-tx emits for Haskell
    `Bool` (`oneOf [constr 0 [], constr 1 []]`, no variant titles). Its `Data`
    encoding is exactly the builtin boolean's, so schemas of this shape map to
    `.bool` instead of a named type. -/
private def isBoolShapeDef (defn : Lean.Json) : Bool :=
  let arr := match defn.getObjVal? "anyOf" with
    | .ok (.arr a) => some a
    | _ => match defn.getObjVal? "oneOf" with | .ok (.arr a) => some a | _ => none
  match arr with
  | some #[v0, v1] =>
    let isCtor (v : Lean.Json) (i : Nat) : Bool :=
      (match v.getObjVal? "dataType" with | .ok (.str "constructor") => true | _ => false) &&
      (getOptStr v "title").isNone &&
      (match v.getObjVal? "index" with | .ok (.num n) => n.mantissa.toNat == i | _ => false) &&
      (match v.getObjVal? "fields" with | .ok (.arr f) => f.isEmpty | .error _ => true | _ => false)
    isCtor v0 0 && isCtor v1 1
  | _ => false

/-- A definition is "nameable" — worth emitting as its own Lean type — when it
    is a sum type (`anyOf`/`oneOf`) or a single constructor (record), except
    for the `Bool`-shaped sum which maps to the builtin boolean. -/
private def isNameableDef (defn : Lean.Json) : Bool :=
  ((defn.getObjVal? "anyOf" |>.toOption.isSome) ||
   (defn.getObjVal? "oneOf" |>.toOption.isSome) ||
   (match defn.getObjVal? "dataType" with | .ok (.str "constructor") => true | _ => false)) &&
  !isBoolShapeDef defn

/-- The Lean-facing name of a definition: its `title`, falling back to the key. -/
private def defTypeName (key : String) (defn : Lean.Json) : String :=
  (getOptStr defn "title").getD key

private partial def parseSchemaType (defs : Lean.Json) (j : Lean.Json) (depth : Nat) : PlutusType :=
  if depth == 0 then .opaque "<max depth>" else
  match j.getObjVal? "$ref" with
  | .ok (.str ref) =>
    let defsPrefix := "#/definitions/"
    let key := if ref.startsWith defsPrefix
                 then decodeJsonPointer (ref.drop defsPrefix.length)
                 else ref
    match defs.getObjVal? key with
    -- Preserve the name of nameable definitions so they can reference an
    -- emitted Lean type instead of inlining (and collapsing to `Data`).
    | .ok defn => if isNameableDef defn then .named (defTypeName key defn)
                  else parseSchemaType defs defn (depth - 1)
    | _        => .opaque key
  | _ =>
  let anyOneOf := match j.getObjVal? "anyOf" with
    | .ok (.arr a) => some a
    | _ => match j.getObjVal? "oneOf" with
      | .ok (.arr a) => some a
      | _ => none
  match anyOneOf with
  | some arr =>
    let variants := arr.toList.map (parseSchemaType defs · (depth - 1))
    match variants with
    | [single] => single
    | [.constr none 0 [], .constr none 1 []] => .bool
    | _        => .anyOf variants
  | none =>
  match j.getObjVal? "dataType" with
  | .ok (.str dt) =>
    match dt with
    | "#integer" | "integer" => .integer
    | "#bytes" | "#bytestring" | "bytestring" | "bytes" => .bytestring
    | "#string"    => .string
    | "#boolean"   => .bool
    | "#unit"      => .unit
    | "#void"      => .void
    | "#list" | "list" =>
      let items := match j.getObjVal? "items" with
        | .ok i => parseSchemaType defs i (depth - 1)
        | _     => .data
      .list items
    | "map" =>
      let keys   := match j.getObjVal? "keys"   with | .ok k => parseSchemaType defs k (depth-1) | _ => .data
      let values := match j.getObjVal? "values" with | .ok v => parseSchemaType defs v (depth-1) | _ => .data
      .map keys values
    | "#pair" | "pair" =>
      let left  := match j.getObjVal? "left"  with | .ok l => parseSchemaType defs l (depth-1) | _ => .data
      let right := match j.getObjVal? "right" with | .ok r => parseSchemaType defs r (depth-1) | _ => .data
      .pair left right
    | "constructor" =>
      let title  := getOptStr j "title"
      let index  := match j.getObjVal? "index" with
        | .ok (.num n) => n.mantissa.toNat
        | _            => 0
      let fields := match j.getObjVal? "fields" with
        | .ok (.arr arr) =>
          arr.toList.map fun f =>
            let ftitle  := getOptStr f "title"
            let fschema := match f.getObjVal? "schema" with | .ok s => s | _ => f
            (ftitle, parseSchemaType defs fschema (depth - 1))
        | _ => []
      .constr title index fields
    | _ => .opaque dt
  | _ =>
  match getOptStr j "title" with
  | some "Data" => .data
  | _           => .data

/-- Extract the Lean-friendly type name from a `$ref` by looking up the
    definition's `"title"` field, falling back to the decoded key. -/
private def extractTypeName (defs : Lean.Json) (schema : Lean.Json) : Option String :=
  match schema.getObjVal? "$ref" with
  | .ok (.str ref) =>
    let defsPrefix := "#/definitions/"
    if ref.startsWith defsPrefix then
      let key := decodeJsonPointer (ref.drop defsPrefix.length)
      let fromTitle := match defs.getObjVal? key with
        | .ok defn => getOptStr defn "title"
        | _        => none
      some (fromTitle.getD key)
    else none
  | _ => none

private def parseSchemaInfo (defs : Lean.Json) (j : Lean.Json) : SchemaInfo :=
  let schema := match j.getObjVal? "schema" with | .ok s => s | _ => j
  { title    := getOptStr j "title"
    typeName := extractTypeName defs schema
    ptype    := parseSchemaType defs schema 20 }

-- ---------------------------------------------------------------------------
-- Blueprint parsing
-- ---------------------------------------------------------------------------

private def parsePreamble (j : Lean.Json) : Except String BlueprintPreamble := do
  return {
    title         := ← getStr j "title"
    description   := getOptStr j "description"
    version       := ← getStr j "version"
    plutusVersion := ← getStr j "plutusVersion"
    license       := getOptStr j "license"
  }

private def parseArgEncoding : String → ArgEncoding
  | "asData"  => .asData
  | "asScott" => .asScott
  | name      => .other name

/-- Validate references before type lowering can turn unresolved schemas into Data.
Recursive schemas must be guarded by a constructor or container. -/
private partial def validateArgumentSchema (defs j : Lean.Json) (seen : List (String × Nat) := []) (depth : Nat := 0) : Except String Unit := do
  match j with
  | .obj fields =>
    if (j.getObjVal? "allOf").isOk || (j.getObjVal? "not").isOk then
      throw "argument schema uses unsupported composition"
    if let .ok dtJson := j.getObjVal? "dataType" then
      let .str dt := dtJson | throw "argument dataType must be a string"
      unless ["integer", "#integer", "bytestring", "#bytestring", "bytes", "#string",
              "#boolean", "#unit", "#void", "#bytes", "#list", "#pair", "list", "map", "pair", "constructor"].contains dt do
        throw s!"unsupported argument dataType '{dt}'"
    if let .ok refJson := j.getObjVal? "$ref" then
      let .str ref := refJson | throw "argument $ref must be a string"
      unless ref.startsWith "#/definitions/" do throw "argument $ref must reference local definitions"
      let key := decodeJsonPointer (ref.drop "#/definitions/".length)
      let target ← (defs.getObjVal? key).mapError (fun _ => s!"unresolved argument schema '{key}'")
      if let some prior := seen.lookup key then
        unless depth > prior do throw s!"unguarded recursive argument schema '{key}'"
      else validateArgumentSchema defs target ((key, depth) :: seen) depth
    for (key, value) in fields.toArray do
      if ["items", "keys", "values", "left", "right", "schema"].contains key then
        validateArgumentSchema defs value seen (depth + if ["items", "keys", "values", "left", "right"].contains key then 1 else 0)
      if ["fields", "anyOf", "oneOf", "allOf"].contains key then
        let .arr values := value | throw s!"argument schema '{key}' must be an array"
        for v in values do validateArgumentSchema defs v seen (depth + if key == "fields" then 1 else 0)
  | _ => throw "argument schema must be an object"

/-- Each argument requires a schema; the empty schema explicitly means raw Data. -/
private def parseArgument (defs : Lean.Json) (j : Lean.Json) : Except String ArgumentInfo := do
  let encoding := parseArgEncoding (← getStr j "encoding")
  let schema ← (j.getObjVal? "schema").mapError (fun _ => "argument is missing schema")
  validateArgumentSchema defs schema
  return { encoding, ptype := parseSchemaType defs schema 20 }

/-- A non-negative integer JSON field, rejecting fractional/exponent forms. -/
private def getNatField (j : Lean.Json) (key : String) : Option Nat :=
  match j.getObjVal? key with
  | .ok (.num n) => if n.exponent == 0 && n.mantissa ≥ 0 then some n.mantissa.toNat else none
  | _            => none

private def parseBudget (j : Lean.Json) : Except String BudgetInfo :=
  match getNatField j "steps" with
  | some n =>
    if (j.getObjVal? "exCPU").isOk || (j.getObjVal? "exMem").isOk then
      .error "steps and ledger execution units are mutually exclusive"
    else match getOptStr j "semantics" with
    | none => .ok (.steps n)
    | some sem => if ["A", "B", "C", "D", "E"].contains sem then .ok (.semanticSteps n sem)
                  else .error "semantics must be A, B, C, D, or E"
  | none   =>
    match getNatField j "exCPU", getNatField j "exMem" with
    | some c, some m => .ok (.exUnits c m)
    | _,      _      =>
      .error "'budget' must be either {\"steps\": n} or {\"exCPU\": n, \"exMem\": m} \
with non-negative integers"

def interfaceSchemaUri : String :=
  "https://cips.cardano.org/cips/cip57/extensions/compiled-interface/v1/schema.json"

/-- Determine only the outer wire representation, without expanding data fields. -/
private partial def rootEncoding (defs schema : Json) (seen : List String := []) : Except String ArgEncoding := do
  if let some ref := getOptStr schema "$ref" then
    unless ref.startsWith "#/definitions/" do throw "nonlocal schema reference"
    let key := decodeJsonPointer (ref.drop 14)
    if seen.contains key then throw "unguarded recursive schema encoding"
    return ← rootEncoding defs (← defs.getObjVal? key) (key :: seen)
  let kind := (getOptStr schema "dataType").getD ""
  if kind.startsWith "#" then return .asNative kind
  for key in ["oneOf", "anyOf"] do
    if let .ok (.arr children) := schema.getObjVal? key then
      for child in children do
        unless (← rootEncoding defs child seen) == .asData do
          throw "native values cannot occur inside Data alternatives"
  return .asData

/-- Validate a finite schema graph. Only cycles crossing a data field/container
are productive. Every child still has its own representation checked. -/
private partial def schemaEncoding (defs schema : Json)
    (seen : List (String × Nat) := []) (depth : Nat := 0) : Except String ArgEncoding := do
  if let some ref := getOptStr schema "$ref" then
    if ["dataType", "anyOf", "oneOf", "allOf", "not", "encoding", "constructors"].any (fun k => (schema.getObjVal? k).isOk) then
      throw "ambiguous schema representation beside reference"
    unless ref.startsWith "#/definitions/" do throw "nonlocal schema reference"
    let key := decodeJsonPointer (ref.drop 14)
    let target ← (defs.getObjVal? key).mapError (fun _ => s!"unresolved argument schema '{key}'")
    if let some prior := seen.lookup key then
      unless depth > prior do throw "unguarded recursive schema encoding"
      return ← rootEncoding defs target
    return ← schemaEncoding defs target ((key, depth) :: seen) depth
  if (schema.getObjVal? "allOf").isOk || (schema.getObjVal? "not").isOk then
    throw "unsupported schema composition"
  let kind := (getOptStr schema "dataType").getD ""
  if kind != "" && ((schema.getObjVal? "anyOf").isOk || (schema.getObjVal? "oneOf").isOk) then
    throw "ambiguous schema representation beside dataType"
  if kind == "#scott" then throw "Scott encoding is not supported by this checking profile"
  unless ["", "integer", "bytes", "list", "map", "constructor", "#integer", "#bytes", "#unit", "#boolean", "#string", "#list", "#pair"].contains kind do
    throw s!"unsupported parameter dataType '{kind}'"
  for key in ["items", "keys", "values", "left", "right", "fields", "oneOf", "anyOf"] do
    if let .ok child := schema.getObjVal? key then
      let children := match child with | .arr a => a | _ => #[child]
      let next := depth + if ["items", "keys", "values", "left", "right", "fields"].contains key then 1 else 0
      for c in children do
        unless (← schemaEncoding defs c seen next) == .asData do
          throw "native values cannot occur inside Data containers or Data alternatives"
  return ← rootEncoding defs schema

/-- Whether lowering would require a recursive generated host type. Such inputs
stay raw Data, preserving arbitrary finite depth and the malformed-input domain. -/
private partial def recursiveSchema (defs schema : Json) (seen : List String := []) : Bool :=
  if let some ref := getOptStr schema "$ref" then
    let key := decodeJsonPointer (ref.drop 14)
    seen.contains key || ((defs.getObjVal? key).toOption.any fun target => recursiveSchema defs target (key :: seen))
  else ["items", "keys", "values", "left", "right", "fields", "oneOf", "anyOf"].any fun key =>
    match schema.getObjVal? key with
    | .ok (.arr a) => a.any (recursiveSchema defs · seen)
    | .ok child => recursiveSchema defs child seen
    | _ => false

/-- Standalone assurance functions use the same wire schema vocabulary. Data
ADTs stay raw Data at this boundary, so no decoder silently narrows their domain. -/
def parseFunctionWire (schema : Json) (defs : Json := Json.mkObj []) : Except String ArgumentInfo := do
  let encoding ← schemaEncoding defs schema
  validateArgumentSchema defs schema
  let ptype := match encoding with
    | .asData => PlutusType.data
    | .asNative "#list" => .list .data
    | .asNative "#pair" => .pair .data .data
    | _ => parseSchemaType defs schema 20
  return { encoding, ptype }

private def purposeMatches (slot : Json) (purpose : String) : Bool :=
  match slot.getObjVal? "purpose" with
  | .error _ => true
  | .ok (.str p) => p == purpose
  | .ok p => ((p.getObjValAs? (Array String) "oneOf").toOption.getD #[]).contains purpose

private def selectSlot (v : Json) (role purpose : String) : Except String Json := do
  let slot ← v.getObjVal? role
  match slot.getObjVal? "oneOf" with
  | .ok (.arr choices) =>
    let selected :=  choices.filter (purposeMatches · purpose)
    unless selected.size == 1 do throw "ambiguous purpose-specific runtime schema"
    return ← selected[0]!.getObjVal? "schema"
  | _ =>
    unless purposeMatches slot purpose do throw "runtime schema purpose mismatch"
    slot.getObjVal? "schema"

private def parseInterface (defs v : Json) (version : String) : Except String (Array (String × Array ArgumentInfo)) := do
  let iface ← v.getObjVal? "interface"
  let convention ← getStr iface "callingConvention"
  unless convention == "ledger-" ++ version && ["v1", "v2", "v3"].contains version do
    throw "calling convention does not match Plutus language"
  let params := ((v.getObjValAs? (Array Json) "parameters").toOption).getD #[]
  let invocations ← iface.getObjValAs? (Array Json) "invocations"
  let mut results := #[]
  let mut purposes : List String := []
  for inv in invocations do
    let purpose ← getStr inv "purpose"
    if purposes.contains purpose then throw "duplicate invocation purpose"
    purposes := purpose :: purposes
    unless ["spend", "mint", "withdraw", "publish", "vote", "propose"].contains purpose do throw "unknown invocation purpose"
    if version != "v3" && ["vote", "propose"].contains purpose then throw "purpose requires Plutus V3"
    let suffix := if version == "v3" then ["context"] else if purpose == "spend" then ["datum", "redeemer", "context"] else ["redeemer", "context"]
    let args ← inv.getObjValAs? (Array Json) "arguments"
    unless args.size == params.size + suffix.length do throw "incomplete invocation arguments"
    let mut parsed : Array ArgumentInfo := #[]
    for i in [:params.size] do
      let a := args[i]!
      unless getOptStr a "role" == some "parameter" && getOptStr a "source" == some s!"/parameters/{i}" do
        throw "parameter order/reference mismatch"
      unless purposeMatches params[i]! purpose do throw "parameter purpose mismatch"
      let schema ← params[i]!.getObjVal? "schema"
      let encoding ← schemaEncoding defs schema
      validateArgumentSchema defs schema
      let ptype := match encoding with
        | .asNative "#list" => PlutusType.list .data
        | .asNative "#pair" => PlutusType.pair .data .data
        | .asData => if recursiveSchema defs schema then .data else parseSchemaType defs schema 20
        | _ => parseSchemaType defs schema 20
      parsed := parsed.push { encoding, ptype }
    for i in [:suffix.length] do
      let role := suffix[i]!
      let a := args[params.size + i]!
      unless getOptStr a "role" == some role do throw "invalid runtime argument order"
      if role == "context" then
        if (a.getObjVal? "source").isOk then throw "context cannot override its source"
      else
        unless getOptStr a "source" == some ("/" ++ role) do throw "invalid runtime argument source"
      parsed := parsed.push { encoding := .asData, ptype := .data }
    -- V3 payload descriptions remain Data even though they are not positional.
    for role in ["datum", "redeemer"] do
      if (v.getObjVal? role).isOk then
        let schema ← selectSlot v role purpose
        unless (← schemaEncoding defs schema) == .asData do throw "runtime payload must be Data"
      else if suffix.contains role then throw s!"missing runtime {role}"
    results := results.push (purpose, parsed)
  return results

private def parseValidator (defs : Lean.Json) (extended : Bool) (version : String) (j : Lean.Json) : Except String BlueprintValidator := do
  let title ← getStr j "title"
  let datum      := match j.getObjVal? "datum"      with | .ok d => some (parseSchemaInfo defs d) | _ => none
  let redeemer   := match j.getObjVal? "redeemer"   with | .ok r => some (parseSchemaInfo defs r) | _ => none
  let parameters := match j.getObjVal? "parameters" with
    | .ok (.arr arr) => arr.map (parseSchemaInfo defs)
    | _              => #[]
  let arguments ← match j.getObjVal? "arguments" with
    | .ok (.arr arr) =>
      some <$> arr.mapM fun a =>
        (parseArgument defs a).mapError (s!"validator '{title}': 'arguments': {·}")
    | .ok _    => .error s!"validator '{title}': 'arguments' must be an array"
    | .error _ => pure none
  let budget ← match j.getObjVal? "budget" with
    | .ok b    => some <$> (parseBudget b).mapError (s!"validator '{title}': {·}")
    | .error _ => pure none
  return {
    title
    id           := getOptStr j "id"
    description  := getOptStr j "description"
    compiledCode := getOptStr j "compiledCode"
    hash         := getOptStr j "hash"
    datum
    redeemer
    parameters
    arguments
    budget
    invocations := ← if extended then parseInterface defs j version else pure #[]
  }

def parseBlueprint (s : String) : Except String Blueprint := do
  let json ← Lean.Json.parse s
  let uri := getOptStr json "$schema"
  let extended := uri == some interfaceSchemaUri
  if extended then AssuranceSchema.validateDocument json
  else if uri.isSome && uri != some "https://cips.cardano.org/cips/cip57/schemas/plutus-blueprint.json" then
    throw "unsupported blueprint dialect"
  let preamble ← match json.getObjVal? "preamble" with
    | .ok j    => parsePreamble j
    | .error e => .error s!"missing 'preamble': {e}"
  let defs := match json.getObjVal? "definitions" with | .ok d => d | _ => .null
  let validators ← match json.getObjVal? "validators" with
    | .ok (.arr arr) => arr.mapM (parseValidator defs extended preamble.plutusVersion)
    | .ok _          => .error "'validators' must be an array"
    | .error e       => .error s!"missing 'validators': {e}"
  -- Collect every nameable definition so it can be emitted as a Lean type.
  let namedTypes : List (String × PlutusType) :=
    match defs with
    | .obj o => o.foldl (init := []) (fun acc key defn =>
        if isNameableDef defn then (defTypeName key defn, parseSchemaType defs defn 20) :: acc
        else acc)
    | _ => []
  if extended then
    let ids := validators.toList.filterMap (·.id)
    unless ids.length == ids.eraseDups.length do throw "duplicate validator id"
  return { extended, preamble, validators, namedTypes }

def sanitizeName (s : String) : String :=
  String.mk <| s.data.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- Lean 4 reserved words that a sanitized schema name might collide with. -/
private def leanKeywords : List String :=
  ["end", "type", "class", "structure", "inductive", "instance", "def", "theorem",
   "example", "abbrev", "do", "by", "match", "with", "where", "deriving", "then",
   "else", "fun", "let", "if", "open", "namespace", "section", "variable", "in",
   "at", "from", "import", "return", "try", "catch", "finally", "for", "while",
   "have", "show", "calc", "mutual", "partial", "private", "protected", "macro",
   "syntax", "notation", "attribute", "set_option", "extends", "sorry", "nomatch"]

/-- Wrap an identifier in `«…»` when it is a Lean keyword or starts with a digit,
    so the *generated source* parses. The underlying declaration `Name` (built
    with `Name.mkStr` from the raw sanitized string) is unchanged. -/
private def escapeIdent (s : String) : String :=
  let leadingDigit := (s.get? ⟨0⟩).map Char.isDigit |>.getD false
  if leanKeywords.contains s || leadingDigit then "«" ++ s ++ "»" else s

/-- A field type "degrades to `Data`" when it contains a constructor/sum/opaque
    node the emitter cannot express as a structured Lean type (so it falls back
    to raw `Data`). Used to warn instead of silently dropping structure. -/
private partial def degradesToData : PlutusType → Bool
  | .constr .. | .anyOf .. | .opaque .. => true
  | .named _  => false
  | .list t   => degradesToData t
  | .map k v  => degradesToData k || degradesToData v
  | .pair a b => degradesToData a || degradesToData b
  | _         => false

/-- All named-type references occurring anywhere in a `PlutusType`. -/
private partial def collectNamedRefs : PlutusType → List String
  | .named n           => [n]
  | .list t            => collectNamedRefs t
  | .map k v           => collectNamedRefs k ++ collectNamedRefs v
  | .pair a b          => collectNamedRefs a ++ collectNamedRefs b
  | .anyOf vs          => vs.flatMap collectNamedRefs
  | .constr _ _ fields => fields.flatMap (fun (_, t) => collectNamedRefs t)
  | _                  => []

/-- Order named-type definitions so each type's dependencies come first.
    Returns `(orderedEmittable, droppedNames)`; a type is dropped when it takes
    part in a reference cycle (self-recursion or mutual recursion), together
    with everything transitively depending on it. -/
private partial def topoOrderTypes
    (items : List (String × String × PlutusType)) :
    List (String × String × PlutusType) × List String :=
  let rec go (remaining : List (String × String × PlutusType))
             (done : List String) (acc : List (String × String × PlutusType)) :=
    match remaining with
    | [] => (acc, [])
    | _ =>
      let ready := remaining.filter fun (_, _, pt) =>
        (collectNamedRefs pt).all fun r =>
          let rs := sanitizeName r
          done.contains rs
      if ready.isEmpty then
        (acc, remaining.map (·.1))
      else
        let readyNames := ready.map (·.1)
        let notReady := remaining.filter fun it => !readyNames.contains it.1
        go notReady (done ++ readyNames) (acc ++ ready)
  go items [] []

def plutusVersionToLangExpr (v : String) : Except String Expr :=
  match v with
  | "v1" => .ok (mkConst ``PlutusLanguage.PlutusV1)
  | "v2" => .ok (mkConst ``PlutusLanguage.PlutusV2)
  | "v3" => .ok (mkConst ``PlutusLanguage.PlutusV3)
  | _    => .error s!"Unknown plutusVersion '{v}'"

private def mkAbbrevDecl (name : Name) (type value : Expr) : Declaration :=
  .defnDecl {
    name        := name
    levelParams := []
    type        := type
    value       := value
    hints       := .abbrev
    safety      := .safe
  }

-- ---------------------------------------------------------------------------
-- Expression builders for BlueprintInfo values
-- ---------------------------------------------------------------------------

private def mkOptStrExpr : Option String → Expr
  | .none   => mkApp  (.const ``Option.none [.zero]) (.const ``String [])
  | .some s => mkApp2 (.const ``Option.some [.zero]) (.const ``String []) (mkStrLit s)

mutual
  partial def buildPlutusTypeExpr : PlutusType → Expr
    | .integer    => .const ``PlutusType.integer []
    | .bytestring => .const ``PlutusType.bytestring []
    | .string     => .const ``PlutusType.string []
    | .bool       => .const ``PlutusType.bool []
    | .unit       => .const ``PlutusType.unit []
    | .void       => .const ``PlutusType.void []
    | .data       => .const ``PlutusType.data []
    | .opaque n   => mkApp (.const ``PlutusType.opaque []) (mkStrLit n)
    | .list items => mkApp (.const ``PlutusType.list []) (buildPlutusTypeExpr items)
    | .map k v    => mkApp2 (.const ``PlutusType.map  []) (buildPlutusTypeExpr k) (buildPlutusTypeExpr v)
    | .pair l r   => mkApp2 (.const ``PlutusType.pair []) (buildPlutusTypeExpr l) (buildPlutusTypeExpr r)
    | .named n    => mkApp  (.const ``PlutusType.named  []) (mkStrLit n)
    | .anyOf vs   => mkApp  (.const ``PlutusType.anyOf  []) (buildPTListExpr vs)
    | .constr t i fs =>
        mkAppN (.const ``PlutusType.constr [])
          #[mkOptStrExpr t, mkNatLit i, buildFieldListExpr fs]

  partial def buildPTListExpr (ts : List PlutusType) : Expr :=
    ts.foldr
      (fun t acc => mkApp3 (.const ``List.cons [.zero]) (.const ``PlutusType [])
                           (buildPlutusTypeExpr t) acc)
      (mkApp (.const ``List.nil [.zero]) (.const ``PlutusType []))

  partial def buildFieldListExpr (fields : List (Option String × PlutusType)) : Expr :=
    let pairTyp := mkApp2 (.const ``Prod [.zero, .zero])
                          (mkApp (.const ``Option [.zero]) (.const ``String []))
                          (.const ``PlutusType [])
    fields.foldr
      (fun (t, p) acc =>
        let pair := mkApp4 (.const ``Prod.mk [.zero, .zero])
                           (mkApp (.const ``Option [.zero]) (.const ``String []))
                           (.const ``PlutusType [])
                           (mkOptStrExpr t)
                           (buildPlutusTypeExpr p)
        mkApp3 (.const ``List.cons [.zero]) pairTyp pair acc)
      (mkApp (.const ``List.nil [.zero]) pairTyp)
end

private def buildSchemaInfoExpr (si : SchemaInfo) : Expr :=
  mkAppN (.const ``SchemaInfo.mk [])
    #[mkOptStrExpr si.title, mkOptStrExpr si.typeName, buildPlutusTypeExpr si.ptype]

private def buildOptSchemaInfoExpr : Option SchemaInfo → Expr
  | .none    => mkApp  (.const ``Option.none [.zero]) (.const ``SchemaInfo [])
  | .some si => mkApp2 (.const ``Option.some [.zero]) (.const ``SchemaInfo [])
                       (buildSchemaInfoExpr si)

private def buildSchemaInfoArrayExpr (arr : Array SchemaInfo) : Expr :=
  let nilExpr  := mkApp  (.const ``List.nil  [.zero]) (.const ``SchemaInfo [])
  let listExpr := arr.toList.foldr
    (fun si acc => mkApp3 (.const ``List.cons [.zero]) (.const ``SchemaInfo [])
                          (buildSchemaInfoExpr si) acc)
    nilExpr
  mkApp2 (.const ``Array.mk [.zero]) (.const ``SchemaInfo []) listExpr

-- `optScriptExpr` is the expression for `Option PlutusScript` — a constant reference
-- to the already-emitted script definition, so the AST is not duplicated.
private def buildValidatorInfoExpr (v : BlueprintValidator) (optScriptExpr : Expr) : Expr :=
  mkAppN (.const ``ValidatorInfo.mk [])
    #[mkStrLit v.title, mkOptStrExpr v.id, mkOptStrExpr v.description, mkOptStrExpr v.hash,
      optScriptExpr,
      buildOptSchemaInfoExpr v.datum,
      buildOptSchemaInfoExpr v.redeemer,
      buildSchemaInfoArrayExpr v.parameters]

def buildBlueprintInfoExpr (pre : BlueprintPreamble) (viExprs : Array Expr) : Expr :=
  let nilExpr  := mkApp  (.const ``List.nil  [.zero]) (.const ``ValidatorInfo [])
  let listExpr := viExprs.toList.foldr
    (fun e acc => mkApp3 (.const ``List.cons [.zero]) (.const ``ValidatorInfo []) e acc)
    nilExpr
  let arrExpr  := mkApp2 (.const ``Array.mk [.zero]) (.const ``ValidatorInfo []) listExpr
  mkAppN (.const ``BlueprintInfo.mk [])
    #[mkStrLit pre.title, mkOptStrExpr pre.description, mkStrLit pre.version,
      mkStrLit pre.plutusVersion, mkOptStrExpr pre.license, arrExpr]

-- ---------------------------------------------------------------------------
-- Lean type / IsData instance code generation from PlutusType schemas
-- ---------------------------------------------------------------------------

/-- `open` command added inside every generated namespace block so that
    generated code can use the same short names as `IsData.Basic`. -/
def openDecl : String :=
  "open PlutusCore.Data PlutusCore.Integer PlutusCore.ByteString PlutusCore.IsData"

/-- Map a `PlutusType` to a Lean type name string using the short names
    brought into scope by `openDecl`. Falls back to `Data` for complex types. -/
private partial def plutusTypeToTypeStr : PlutusType → String
  | .integer    => "Integer"
  | .bytestring => "ByteString"
  | .bool       => "Bool"
  | .unit | .void => "Unit"
  | .data       => "Data"
  | .string     => "String"
  | .list t     => "(List " ++ plutusTypeToTypeStr t ++ ")"
  | .pair a b   => "(" ++ plutusTypeToTypeStr a ++ " × " ++ plutusTypeToTypeStr b ++ ")"
  | .map k v    => "(List (" ++ plutusTypeToTypeStr k ++ " × " ++ plutusTypeToTypeStr v ++ "))"
  | .named n    => escapeIdent (sanitizeName n)
  | _           => "Data"

/-- Generate a Lean expression string that encodes `fieldExpr` as `Data`.
    Recurses through `list`/`map`/`pair` so a `map` at any depth targets the
    dedicated `Data.Map` shape rather than the generic `List`-of-`Constr`. -/
private partial def encodeFieldStr (fieldExpr : String) : PlutusType → String
  | .integer    => "Data.I (" ++ fieldExpr ++ ")"
  | .bytestring => "Data.B (" ++ fieldExpr ++ ")"
  | .string     => "Data.B { data := (" ++ fieldExpr ++ ") }"
  | .bool       => "if (" ++ fieldExpr ++ ") then Data.Constr 1 [] else Data.Constr 0 []"
  | .unit | .void => "Data.Constr 0 []"
  | .data       => "(" ++ fieldExpr ++ ")"
  | .list t     =>
      "Data.List ((" ++ fieldExpr ++ ").map (fun _x => " ++ encodeFieldStr "_x" t ++ "))"
  | .map k v    =>
      "Data.Map ((" ++ fieldExpr ++ ").map (fun (_a, _b) => (" ++
        encodeFieldStr "_a" k ++ ", " ++ encodeFieldStr "_b" v ++ ")))"
  | .pair a b   =>
      "Data.Constr 0 [" ++ encodeFieldStr ("(" ++ fieldExpr ++ ").1") a ++ ", " ++
        encodeFieldStr ("(" ++ fieldExpr ++ ").2") b ++ "]"
  | _           => "IsData.toData (" ++ fieldExpr ++ ")"

/-- Generate a Lean expression string that decodes a `Data` value.
    Produces `Option T` where `T = plutusTypeToTypeStr ftype`. -/
private partial def decodeFieldStr (dataExpr : String) : PlutusType → String
  | .integer    => "(match " ++ dataExpr ++ " with | Data.I _x => some _x | _ => none)"
  | .bytestring => "(match " ++ dataExpr ++ " with | Data.B _x => some _x | _ => none)"
  | .string     => "(match " ++ dataExpr ++ " with | Data.B _x => some _x.data | _ => none)"
  | .bool       => "(match " ++ dataExpr ++ " with | Data.Constr 0 [] => some false | Data.Constr 1 [] => some true | _ => none)"
  | .unit | .void => "(match " ++ dataExpr ++ " with | Data.Constr 0 [] => some () | _ => none)"
  | .data       => "(some " ++ dataExpr ++ ")"
  | .list t     =>
      "(match " ++ dataExpr ++ " with | Data.List _xs => _xs.mapM (fun _x => " ++
        decodeFieldStr "_x" t ++ ") | _ => none)"
  | .map k v    =>
      "(match " ++ dataExpr ++ " with | Data.Map _m => _m.mapM (fun (_a, _b) => (" ++
        decodeFieldStr "_a" k ++ ").bind (fun _k => (" ++ decodeFieldStr "_b" v ++
        ").bind (fun _v => some (_k, _v)))) | _ => none)"
  | .pair a b   =>
      "(match " ++ dataExpr ++ " with | Data.Constr 0 [_a, _b] => (" ++
        decodeFieldStr "_a" a ++ ").bind (fun _x => (" ++ decodeFieldStr "_b" b ++
        ").bind (fun _y => some (_x, _y))) | _ => none)"
  | t           => "(IsData.fromData " ++ dataExpr ++ " : Option " ++ plutusTypeToTypeStr t ++ ")"

/-- Parse a Lean command from a generated string (for code gen). -/
def parseCommand (s : String) : CommandElabM Syntax := do
  match Lean.Parser.runParserCategory (← getEnv) `command s with
  | .ok stx  => return stx
  | .error e => throwError s!"Failed to parse generated command:\n{e}\n---\n{s}"

/-- Parse a *sequence* of Lean commands from a string, as the frontend does.
    `parseCommand` insists on a single command consuming the whole input, which
    is not enough for externally supplied blocks of several declarations (e.g.
    an assurance document's formal fragments). `label` names the source in
    parse-error messages. -/
def parseCommands (label : String) (s : String) : CommandElabM (Array Syntax) := do
  let inputCtx := Lean.Parser.mkInputContext s label
  let pmctx : Lean.Parser.ParserModuleContext :=
    { env           := ← getEnv
      options       := ← getOptions
      currNamespace := ← getCurrNamespace
      openDecls     := ← getOpenDecls }
  let mut state    : Lean.Parser.ModuleParserState := {}
  let mut msgs     : Lean.MessageLog := {}
  let mut stxs     : Array Syntax := #[]
  let mut terminal : Syntax := .missing
  repeat
    let (stx, state', msgs') := Lean.Parser.parseCommand inputCtx pmctx state msgs
    state := state'
    msgs  := msgs'
    -- `isTerminalCommand` also fires on `import` / `#exit`, which would
    -- silently truncate the rest of the block; `terminal` lets us reject those.
    if Lean.Parser.isTerminalCommand stx then
      terminal := stx
      break
    stxs := stxs.push stx
  if msgs.hasErrors then
    let texts ← msgs.toList.mapM fun m => m.toString
    throwError s!"Failed to parse {label}:\n{String.intercalate "\n" texts}"
  unless terminal.isOfKind ``Lean.Parser.Command.eoi do
    throwError s!"{label}: `import` and `#exit` are not allowed here; the rest of the \
block would be silently dropped."
  return stxs

/-- Run `action` with the namespace temporarily set to `ns` (absolute path).
    Saves and restores the full scope stack so that opens added by `action`
    don't leak into the caller's namespace, and any exception still restores. -/
def withTempNamespace {α : Type} (ns : Name) (action : CommandElabM α) : CommandElabM α := do
  let savedScopes := (← get).scopes
  modifyScope fun s => { s with currNamespace := ns }
  try
    action
  finally
    modify fun st => { st with scopes := savedScopes }

-- ---------------------------------------------------------------------------
-- Emit a struct type (single constructor, named fields) + IsData instance.
-- ---------------------------------------------------------------------------

private def emitStructType (ns : Name) (typeName : String) (idx : Nat)
    (fields : List (Option String × PlutusType)) : CommandElabM Unit := do
  let shortName := sanitizeName typeName
  if shortName.isEmpty then return
  -- Only generate when every field has a name
  let namedFields := fields.filterMap fun (mname, pt) => mname.map (·, pt)
  -- Positional (unnamed) fields can't become a Lean record: warn and skip.
  if namedFields.length != fields.length then
    logWarning s!"Blueprint: record '{typeName}' has positional (unnamed) fields; \
no Lean type emitted (the slot stays raw Data)."
    return
  -- A genuinely empty constructor (Unit/Void) needs no Lean type — skip quietly.
  if namedFields.isEmpty then return
  -- Skip if already defined
  if (← getEnv).find? (Name.mkStr ns shortName) |>.isSome then return

  -- Warn for every field that could not be given a structured type.
  for (fname, ftype) in namedFields do
    if degradesToData ftype then
      logWarning s!"Blueprint: field '{fname}' of '{typeName}' contains a \
sum-of-products / nested record not yet emitted; typed as Data."

  let esc := escapeIdent shortName
  let fieldLines := namedFields.foldl (fun acc (fname, ftype) =>
    acc ++ "  " ++ escapeIdent (sanitizeName fname) ++ " : " ++ plutusTypeToTypeStr ftype ++ "\n") ""

  -- toData body using short names from openDecl
  let encLines := namedFields.map fun (fname, ftype) =>
    encodeFieldStr ("d." ++ escapeIdent (sanitizeName fname)) ftype
  let toDataBody :=
    "Data.Constr " ++ toString idx ++
    " [" ++ String.intercalate ", " encLines ++ "]"

  -- fromData: pattern match on Constr idx [_v0, _v1, ...]
  let varNames := (List.range namedFields.length).map fun i => "_v" ++ toString i
  let patVarList := "[" ++ String.intercalate ", " varNames ++ "]"
  let pat := "Data.Constr " ++ toString idx ++ " " ++ patVarList

  -- Build bind chain from right (innermost) to left (outermost)
  let fieldsWithIdx := (List.range namedFields.length).zip namedFields
  let innermost :=
    "some (" ++ esc ++ ".mk " ++
    String.intercalate " " (namedFields.map (escapeIdent ∘ sanitizeName ∘ Prod.fst)) ++ ")"
  let chain := fieldsWithIdx.reverse.foldl
    (fun acc (i, fname, ftype) =>
      "(" ++ decodeFieldStr ("_v" ++ toString i) ftype ++ ").bind (fun " ++ escapeIdent (sanitizeName fname) ++ " => " ++ acc ++ ")")
    innermost

  let fromDataBody :=
    "| " ++ pat ++ " => " ++ chain ++ "\n" ++
    "        | _ => none"

  withTempNamespace ns do
    -- Bring PlutusCore short names into scope for the declarations below
    elabCommand (← parseCommand openDecl)
    elabCommand (← parseCommand (
      "structure " ++ esc ++ " where\n" ++ fieldLines ++ "  deriving Repr"))
    elabCommand (← parseCommand (
      "instance : IsData " ++ esc ++ " where\n" ++
      "  toData d := " ++ toDataBody ++ "\n" ++
      "  fromData x := match x with\n" ++
      "        " ++ fromDataBody))

-- ---------------------------------------------------------------------------
-- Emit a sum-of-products inductive (anyOf with any constructors, fielded or
-- not) + IsData instance. Enums are the no-field special case.
-- ---------------------------------------------------------------------------

private def emitSopType (ns : Name) (typeName : String)
    (variants : List PlutusType) : CommandElabM Unit := do
  let shortName := sanitizeName typeName
  if shortName.isEmpty then return
  if (← getEnv).find? (Name.mkStr ns shortName) |>.isSome then return
  -- Each variant must be a constructor; keep (title?, index, fieldTypes).
  let parsed : List (Option String × Nat × List PlutusType) := variants.filterMap fun
    | .constr t idx fields => some (t, idx, fields.map (·.2))
    | _ => none
  if parsed.length != variants.length then
    logWarning s!"Blueprint: sum type '{typeName}' has variants that are not \
constructors; no Lean type emitted (the slot stays raw Data)."
    return
  -- Constructor names: the sanitized variant title when present (suffixed with
  -- the constructor index when several variants share one — plutus-tx reuses
  -- the type name), `mk` for a single untitled variant (a record), and
  -- `c<index>` otherwise.
  let sanitizedTitles := parsed.filterMap fun (t, _, _) => t.map sanitizeName
  let ctors : List (String × Nat × List PlutusType) := parsed.map fun (t, idx, ftypes) =>
    let cname := match t.map sanitizeName with
      | some s => if sanitizedTitles.count s > 1 then s!"{s}_{idx}" else s
      | none   => if parsed.length == 1 then "mk" else s!"c{idx}"
    (cname, idx, ftypes)

  let esc := escapeIdent shortName
  -- Per-constructor: field binders, encode list, decode bind-chain.
  let ctorDecls := ctors.foldl (fun acc (cname, _, ftypes) =>
    let binders := (List.range ftypes.length).foldl (fun b j =>
      b ++ " (_f" ++ toString j ++ " : " ++ plutusTypeToTypeStr ftypes[j]! ++ ")") ""
    acc ++ "  | " ++ escapeIdent cname ++ binders ++ "\n") ""
  let toArms := ctors.foldl (fun acc (cname, idx, ftypes) =>
    let vars := (List.range ftypes.length).foldl (fun b j => b ++ " _f" ++ toString j) ""
    let encs := (List.range ftypes.length).map fun j => encodeFieldStr ("_f" ++ toString j) ftypes[j]!
    acc ++ "    | ." ++ escapeIdent cname ++ vars ++ " => Data.Constr " ++ toString idx ++
      " [" ++ String.intercalate ", " encs ++ "]\n") ""
  let fromArms := ctors.foldl (fun acc (cname, idx, ftypes) =>
    let n := ftypes.length
    let patVars := "[" ++ String.intercalate ", " ((List.range n).map (fun j => "_v" ++ toString j)) ++ "]"
    let ctorApp := "some (." ++ escapeIdent cname ++
      (List.range n).foldl (fun b j => b ++ " _f" ++ toString j) "" ++ ")"
    let chain := (List.range n).reverse.foldl (fun inner j =>
      "(" ++ decodeFieldStr ("_v" ++ toString j) ftypes[j]! ++ ").bind (fun _f" ++ toString j ++ " => " ++ inner ++ ")")
      ctorApp
    acc ++ "    | Data.Constr " ++ toString idx ++ " " ++ patVars ++ " => " ++ chain ++ "\n") ""

  withTempNamespace ns do
    elabCommand (← parseCommand openDecl)
    elabCommand (← parseCommand (
      "inductive " ++ esc ++ " where\n" ++ ctorDecls ++ "  deriving Repr"))
    elabCommand (← parseCommand (
      "instance : IsData " ++ esc ++ " where\n" ++
      "  toData x := match x with\n" ++ toArms ++
      "  fromData x := match x with\n" ++ fromArms ++
      "    | _ => none"))

-- ---------------------------------------------------------------------------
-- Dispatch: choose which generator to call for a given type / schema slot.
-- ---------------------------------------------------------------------------

/-- Emit a Lean type + `IsData` instance for one named definition or inline slot. -/
private def emitNamedType (ns : Name) (typeName : String) (pt : PlutusType) : CommandElabM Unit := do
  match pt with
  | .anyOf variants => emitSopType ns typeName variants
  | .constr _ _ [] => return          -- Unit/Void-like: no Lean type needed
  | .constr _ idx fields =>
    -- Named-field record → structure; positional fields → single-ctor inductive.
    if fields.all (·.1.isSome) then emitStructType ns typeName idx fields
    else emitSopType ns typeName [pt]
  | _ => return

/-- Emit the type for a datum/redeemer/parameter slot. `.named` slots are
    already produced by the named-definitions pass, so they are skipped here. -/
private def tryEmitSchemaType (ns : Name) (si : SchemaInfo) : CommandElabM Unit := do
  let some typeName := si.typeName | return
  match si.ptype with
  | .named _ => return
  | pt => emitNamedType ns typeName pt

-- ---------------------------------------------------------------------------
-- Applied-validator wrapper: apply the compiled program to its declared
-- `arguments` and run the CEK machine for the declared step budget.
-- ---------------------------------------------------------------------------

/-- Why no applied-validator wrapper can be emitted for a validator that
    declares `arguments` — or `none` when one can. Every reason names the
    blueprint feature that blocks it; nothing is guessed or defaulted. -/
def wrapperBlocker (args : Array ArgumentInfo) (budget : Option BudgetInfo) : Option String :=
  match args.findSome? (fun a =>
      match a.encoding with
      | .asData     => none
      | .asNative kind =>
        if ["#integer", "#bytes", "#string", "#boolean", "#unit", "#list", "#pair"].contains kind then none
        else some s!"unsupported native encoding '{kind}'"
      | .asScott    => some "an argument declares encoding 'asScott', and this package has \
no Scott encoder (there is no `IsScott` class here or in `CardanoLedgerApi`), so the applied \
term would have to be guessed"
      | .other name => some s!"an argument declares the unknown encoding '{name}'") with
  | some why => some why
  | none =>
    match budget with
    | some (.steps _) | some (.semanticSteps ..) => none
    | some (.exUnits c m) =>
      some s!"'budget' is given as ledger execution units (exCPU {c}, exMem {m}), and there \
is no conversion from execution units to the CEK step count `cekExecuteProgram` takes"
    | none =>
      some "the validator declares no 'budget', so there is no CEK step count to run with"

/-- Source text turning wrapper binder `varName` into the `Term` the program is
    applied to, under the `asData` encoding. A `Data` argument is injected
    directly rather than through `IsData.toData`, so the emitted term is
    syntactically the one hand-written CEK properties pass. -/
private def argToTermStr (varName : String) : PlutusType → String
  | .data =>
    "PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Data " ++ varName ++ ")"
  | _ =>
    "PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Data (IsData.toData " ++
      varName ++ "))"

/-- Emit `<ns>.<wrapperName> : … → State`, applying the program of the
    already-emitted `<ns>.<scriptName> : PlutusScript` to its encoded arguments
    and running the CEK machine for `steps` steps.

    Callers must have checked `wrapperBlocker` first. Data arguments use IsData;
    native arguments use their declared builtin constant representation. -/
def emitAppliedWrapper (ns : Name) (wrapperName scriptName : String)
    (args : Array ArgumentInfo) (steps : Nat) (semantics : String := "E") : CommandElabM Unit := do
  let idxs := List.range args.size
  let binders := String.join <| idxs.map fun i =>
    " (a" ++ toString i ++ " : " ++ plutusTypeToTypeStr args[i]!.ptype ++ ")"
  let terms := String.intercalate ", " <| idxs.map fun i =>
    let varName := "a" ++ toString i
    match args[i]!.encoding with
    | .asNative kind =>
      let ctor := match kind with
        | "#integer" => "Integer" | "#bytes" => "ByteString" | "#string" => "String"
        | "#boolean" => "Bool" | "#list" => "ConstDataList" | "#pair" => "PairData" | _ => "Unit"
      let payload := if kind == "#unit" then "" else " " ++ varName
      "PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const." ++ ctor ++ payload ++ ")"
    | _ => argToTermStr varName args[i]!.ptype
  let src :=
    "/-- Applied `" ++ wrapperName ++ "`: the compiled program from the blueprint, applied \
to its declared `arguments` and run on the CEK machine for " ++ toString steps ++ " steps. -/\n" ++
    "def " ++ escapeIdent wrapperName ++ binders ++ " : PlutusCore.UPLC.CekMachine.State :=\n" ++
    "  PlutusCore.UPLC.CekMachine.cekExecuteProgramWithSemanticVariant " ++
      "PlutusCore.Default.Internal.BuiltinSemanticsVariant.defaultFunSemanticsVariant" ++ semantics ++ " " ++ escapeIdent scriptName ++
      ".script [" ++ terms ++ "] " ++ toString steps
  withTempNamespace ns do
    -- Bring `IsData` / `Data` / `Integer` / `ByteString` short names into scope
    -- (the binder types come from `plutusTypeToTypeStr`).
    elabCommand (← parseCommand openDecl)
    elabCommand (← parseCommand src)

/-- Import a digest-checked function from assurance, retaining CEK state and
exposing an exact return-value predicate (including its wire representation). -/
def emitAssuranceFunction (ns : Name) (id code version : String)
    (args : Array ArgumentInfo) (result : ArgumentInfo) (steps : Nat) (sem : String)
    : CommandElabM Unit := do
  let someId := sanitizeName id
  let raw := someId ++ "_script"
  for name in [someId, raw, someId ++ "_returns"] do
    if (← getEnv).contains (Name.mkStr ns name) then throwError "function binding collision: {name}"
  let prog ← ofExcept (singleCborEncodedScriptFromHex? code)
  let lang ← ofExcept (plutusVersionToLangExpr version)
  liftCoreM <| addAndCompile <| mkAbbrevDecl (Name.mkStr ns raw)
    (mkConst ``PlutusScript) (mkApp2 (mkConst ``PlutusScript.mk) lang (toExpr prog))
  emitAppliedWrapper ns someId raw args steps sem
  let indices := List.range args.size
  let binders := String.join <| indices.map fun i =>
    s!" (a{i} : {plutusTypeToTypeStr args[i]!.ptype})"
  let call := String.join <| indices.map fun i => s!" a{i}"
  let value := match result.encoding with
    | .asNative kind =>
      let ctor := match kind with
        | "#integer" => "Integer" | "#bytes" => "ByteString" | "#string" => "String"
        | "#boolean" => "Bool" | "#list" => "ConstDataList" | "#pair" => "PairData" | _ => "Unit"
      "PlutusCore.UPLC.Term.Const." ++ ctor ++ (if kind == "#unit" then "" else " actual")
    | _ => "PlutusCore.UPLC.Term.Const.Data actual"
  withTempNamespace ns do
    elabCommand (← parseCommand openDecl)
    let equal := if result.encoding == .asNative "#unit" then "True" else "actual = expected"
    elabCommand (← parseCommand s!"def {escapeIdent (someId ++ "_returns")}{binders} (expected : {plutusTypeToTypeStr result.ptype}) : Prop :=\n  match {escapeIdent someId}{call} with\n  | PlutusCore.UPLC.CekMachine.State.Halt (PlutusCore.UPLC.CekValue.CekValue.VCon ({value})) => {equal}\n  | _ => False")

/-- Recompute the CIP-57 script hash from the single-CBOR bytes and language tag. -/
def actualScriptHash (version code : String) : Except String String := do
  let tag ← match version.toLower with
    | "v1" => pure 1 | "v2" => pure 2 | "v3" => pure 3
    | _ => throw s!"unsupported Plutus language '{version}'"
  let some chars := PlutusCore.UPLC.ScriptEncoding.Internal.hexStringToString code.data []
    | throw "invalid compiledCode hex"
  let bytes := UInt8.ofNat tag :: chars.map (fun c => UInt8.ofNat c.toNat)
  return Cryptograph.String.uint8ListToHex (Cryptograph.Blake2b.blake2b_224 bytes)

end Internal

open Internal

/-!
### `#import_blueprints` command

Syntax:
```
#import_blueprints <Namespace> <"path/to/plutus.json">
```

Emits (per validator with `compiledCode`):
- `Namespace.sanitized_title : PlutusScript`
- `Namespace.sanitized_title_hash : String`
- `Namespace.sanitized_title_paramCount : Nat`  (when > 0)
- Lean types + `IsData` instances for datum/redeemer/parameters when the schema
  is a simple struct or enum expressible in built-in Plutus types.
- `Namespace : BlueprintInfo`  (top-level inspectable summary)
-/
syntax (name := import_blueprints) "#import_blueprints" ident str : command

/-- Core of `#import_blueprints`: parse the blueprint file at `filepath` and
    emit every declaration into namespace `ns`. Returns the parsed blueprint so
    other commands (e.g. `#verify_blueprint`) can inspect it. -/
def elabBlueprintImport (ns : Name) (filepath : String)
    (selections : List (String × String × BudgetInfo) := [])
    (applications : List (String × String) := []) : CommandElabM Internal.Blueprint := do
  let content  ← liftM (IO.FS.readFile (System.FilePath.mk filepath))
  let blueprint ← match parseBlueprint content with
    | .ok b    => pure b
    | .error e => throwError s!"Failed to parse blueprint '{filepath}': {e}"

  let blueprint ← if selections.isEmpty then pure blueprint else do
    unless blueprint.extended do throwError "checking context requires compiled-interface dialect"
    let validators ← blueprint.validators.mapM fun v => do
      match selections.find? (fun (id, _, _) => v.id == some id) with
      | none => pure v
      | some (id, purpose, budget) =>
        let some (_, args) := v.invocations.find? (fun i => i.1 == purpose)
          | throwError "checking target selects unknown invocation"
        match applications.lookup id with
        | none => pure { v with arguments := some args, budget := some budget }
        | some code =>
          let hash ← ofExcept (actualScriptHash blueprint.preamble.plutusVersion code)
          pure { v with arguments := some (args.extract v.parameters.size args.size), budget := some budget, compiledCode := some code, hash := some hash, parameters := #[] }
    pure { blueprint with validators }

  -- Reject duplicate or colliding generated bindings before adding declarations.
  let mut names : List String := []
  for v in blueprint.validators do
    for name in ([sanitizeName v.title] ++ (v.id.toList.map Internal.sanitizeName)).eraseDups do
      if names.contains name then throwError s!"duplicate validator binding '{name}'"
      names := name :: names
    if let some code := v.compiledCode then
      let actual ← match actualScriptHash blueprint.preamble.plutusVersion (String.trim code) with
        | .ok h => pure h | .error e => throwError e
      if let some expected := v.hash then
        unless expected == actual do
          throwError s!"Validator '{v.title}': compiledCode hash mismatch (declared {expected}, computed {actual})"

  let langExpr ← match plutusVersionToLangExpr blueprint.preamble.plutusVersion with
    | .ok e    => pure e
    | .error e => throwError e

  -- Emit a standalone Lean type + IsData instance for every nameable
  -- definition, dependencies first so nested references resolve.
  let itemsRaw := blueprint.namedTypes.map fun (tn, pt) => (sanitizeName tn, tn, pt)
  let items := itemsRaw.foldl (fun acc it =>
    if acc.any (·.1 == it.1) then acc else acc ++ [it]) []
  let (ordered, dropped) := topoOrderTypes items
  for nm in dropped do
    logWarning s!"Blueprint: type '{nm}' is part of a reference cycle (recursive type); \
no Lean type emitted (references to it stay raw Data)."
  for (_, tn, pt) in ordered do
    emitNamedType ns tn pt

  let mut viExprs : Array Expr := #[]

  for validator in blueprint.validators do
    -- Emit Lean types for any inline datum / redeemer / parameter slots
    -- (named slots were already produced by the pass above).
    if let some si := validator.datum    then tryEmitSchemaType ns si
    if let some si := validator.redeemer then tryEmitSchemaType ns si
    for si in validator.parameters do      tryEmitSchemaType ns si

    -- Emit PlutusScript (and related) declarations
    match validator.compiledCode with
    | .none =>
      logInfo s!"Blueprint: '{validator.title}' has no compiledCode, skipping"
    | .some code =>
      match singleCborEncodedScriptFromHex? (String.trim code) with
      | .error msg =>
        throwError s!"Blueprint: failed to decode '{validator.title}': {msg}"
      | .ok prog =>
        let sanitized  := sanitizeName validator.title

        -- Decide up front whether an applied-validator wrapper will take the
        -- plain `<sanitized>` name; only then is the script renamed. Skipping
        -- the wrapper must not orphan the plain name.
        let wrapper : Option (Array ArgumentInfo × Nat × String) ←
          match validator.arguments with
          | none      => pure none
          | some args =>
            match wrapperBlocker args validator.budget with
            | some why =>
              logWarning s!"Blueprint: validator '{validator.title}' declares 'arguments', \
but no applied-validator wrapper was emitted: {why}. '{sanitized}' stays bound to the \
unapplied PlutusScript."
              pure none
            | none =>
              match validator.budget with
              | some (.steps n) => pure (some (args, n, "E"))
              | some (.semanticSteps n sem) => pure (some (args, n, sem))
              | _               => pure none   -- unreachable: ruled out by wrapperBlocker
        let scriptShort := if wrapper.isSome then sanitized ++ "_script" else sanitized
        let scriptName  := Name.mkStr ns scriptShort

        let scriptDecl ← liftTermElabM do
          pure <| mkAbbrevDecl scriptName
            (mkConst ``PlutusScript)
            (mkApp2 (mkConst ``PlutusScript.mk) langExpr (toExpr prog))
        liftCoreM <| addAndCompile scriptDecl

        if let .some hash := validator.hash then
          liftCoreM <| addAndCompile <| mkAbbrevDecl
            (Name.mkStr ns (sanitized ++ "_hash")) (mkConst ``String) (mkStrLit hash)

        if validator.parameters.size > 0 then
          liftCoreM <| addAndCompile <| mkAbbrevDecl
            (Name.mkStr ns (sanitized ++ "_paramCount"))
            (mkConst ``Nat) (toExpr validator.parameters.size)

        -- The wrapper takes the plain name and refers to the renamed script.
        if let some (args, steps, sem) := wrapper then
          emitAppliedWrapper ns sanitized scriptShort args steps sem

        -- A stable id is the UAL binding. Preserve title bindings for legacy callers.
        if let some vid := validator.id then
          let stable := sanitizeName vid
          if stable != sanitized then
            withTempNamespace ns do
              elabCommand (← parseCommand s!"abbrev {escapeIdent stable} := {escapeIdent sanitized}")
              if wrapper.isSome then
                withTempNamespace ns do
                  elabCommand (← parseCommand s!"abbrev {escapeIdent (stable ++ "_script")} := {escapeIdent scriptShort}")

        -- Reference the already-emitted constant (avoids duplicating the compiled AST)
        let optScriptExpr :=
          mkApp2 (.const ``Option.some [.zero]) (.const ``PlutusScript [])
                 (.const scriptName [])
        viExprs := viExprs.push (buildValidatorInfoExpr validator optScriptExpr)

  -- Emit top-level BlueprintInfo value
  liftCoreM <| addAndCompile <|
    mkAbbrevDecl ns (mkConst ``BlueprintInfo) (buildBlueprintInfoExpr blueprint.preamble viExprs)

  return blueprint

@[command_elab import_blueprints]
def importBlueprintsImpl : CommandElab := fun stx => do
  let nsIdent  := stx[1]
  let pathLit  := stx[2]
  let some filepath := pathLit.isStrLit? | throwErrorAt pathLit "string literal expected"
  discard <| elabBlueprintImport nsIdent.getId filepath

end PlutusCore.UPLC.BlueprintEncoding
