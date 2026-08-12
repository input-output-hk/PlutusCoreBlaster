import Lean

import Blaster.Command.Syntax
import Cryptograph.Sha2
import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.Utils

namespace PlutusCore.UPLC.BlueprintEncoding.Assurance

open Lean Elab Command
open PlutusCore.UPLC.BlueprintEncoding (elabBlueprintImport)
open PlutusCore.UPLC.BlueprintEncoding.Internal
  (getStr getOptStr openDecl parseCommand withTempNamespace BlueprintValidator)

/-! ## CIP-XXXX Plutus Blueprint Assurance documents

This module implements the `#verify_blueprint` command, the consumer side of
the "Plutus Blueprint Assurance Documents" CIP. An assurance document is a
standalone JSON file making machine-readable claims (properties + evidence)
about validators described in a CIP-57 blueprint.

```
#verify_blueprint <Namespace> "path/to/assurance.json"
#verify_blueprint <Namespace> "path/to/assurance.json" "path/to/plutus.json"
```

The command:
1. parses the assurance document;
2. locates the blueprint — the optional second string overrides
   `blueprint.uri` (required when the URI is remote; there is no network
   access at elaboration time). A local URI is resolved relative to the
   assurance document's directory;
3. checks the blueprint file against `blueprint.hash` when present (sha256);
   a mismatch is an error — the claims were made about a different blueprint;
4. imports the blueprint into `<Namespace>` exactly like
   `#import_blueprints`;
5. binds each property's `scope.validators` entries to blueprint validators
   (by `id`, then by `title`; unknown or ambiguous references are errors) and
   warns when an evidence `scriptHash` no longer matches the blueprint
   validator's `hash` (stale claim);
6. **re-runs every property** whose formal statement is written in Lean:
   the inline `source` must be a Lean term of type `Prop`, and is handed to
   `#blaster` with the expected result taken from the recorded `formal-proof`
   evidence (`verified` → Valid, `falsified` → Falsified). Sources elaborate
   inside `<Namespace>` with the `PlutusCore` prelude opens
   (`Data`, `Integer`, `ByteString`, `IsData`, `UPLC.Utils`, `UPLC.CekMachine`,
   `UPLC.Term`, `UPLC.PlutusScript`), so they can reference the imported
   validators and generated datum/redeemer types directly;
7. reports a summary (re-run / skipped counts).

Properties in other formal languages, statements available only by URI, and
purely natural-language statements are surfaced but not re-run.
-/

/-! ### Document model (mirrors the CIP meta-schema) -/

/-- A content digest: algorithm + lowercase hex digest. -/
structure Digest where
  alg    : String
  digest : String
  deriving Repr, Inhabited

/-- Document-level reference to the blueprint the claims are about. -/
structure BlueprintRef where
  uri  : String
  hash : Option Digest
  deriving Repr, Inhabited

/-- An entry of the `languages` / `tools` registries. -/
structure RegistryEntry where
  name        : String
  version     : String
  uri         : Option String
  description : Option String
  deriving Repr, Inhabited

/-- A machine-readable rendering of a statement, in a declared language. -/
structure FormalStatement where
  /-- Key into the document's `languages` registry. -/
  language : String
  source   : Option String
  uri      : Option String
  deriving Repr, Inhabited

/-- A claim: mandatory natural-language text, optional formal rendering. -/
structure Statement where
  text   : String
  formal : Option FormalStatement
  deriving Repr, Inhabited

/-- Reference to a downloadable evidence artifact. -/
structure ArtifactRef where
  uri       : String
  hash      : Option Digest
  mediaType : Option String
  deriving Repr, Inhabited

/-- One verification run: who checked the property, how, and what came out. -/
structure EvidenceRecord where
  /-- Open enum: `formal-proof`, `property-test`, `unit-test`, `audit`,
      `manual-review`, or any tool-specific value. -/
  method     : String
  verifier   : String
  tool       : Option String
  /-- Closed enum: `verified`, `falsified`, `partial`, `inconclusive`. -/
  outcome    : String
  date       : String
  /-- Blake2b-224 hash of the script the verification actually ran against. -/
  scriptHash : Option String
  artifact   : Option ArtifactRef
  notes      : Option String
  deriving Repr, Inhabited

/-- One property: what is claimed, about which validators, with what evidence. -/
structure Property where
  id              : String
  title           : Option String
  /-- Validator references (blueprint `id`, falling back to `title`). -/
  scopeValidators : List String
  statement       : Statement
  assumptions     : List Statement
  tags            : List String
  evidence        : Array EvidenceRecord
  deriving Repr, Inhabited

/-- A parsed assurance document. -/
structure Document where
  schemaUri   : String
  title       : String
  description : Option String
  version     : Option String
  authors     : List String
  created     : String
  license     : Option String
  blueprint   : BlueprintRef
  languages   : List (String × RegistryEntry)
  tools       : List (String × RegistryEntry)
  properties  : Array Property
  deriving Repr, Inhabited

/-! ### JSON parsing -/

namespace Internal

def parseDigest (j : Lean.Json) : Except String Digest := do
  return { alg := ← getStr j "alg", digest := ← getStr j "digest" }

def parseRegistry (j : Lean.Json) (key : String) :
    Except String (List (String × RegistryEntry)) :=
  match j.getObjVal? key with
  | .ok (.obj o) =>
    let kvs := o.foldl (init := []) (fun acc k v => (k, v) :: acc)
    kvs.reverse.mapM fun (k, v) => do
      let entry : RegistryEntry :=
        { name        := ← getStr v "name"
          version     := ← getStr v "version"
          uri         := getOptStr v "uri"
          description := getOptStr v "description" }
      return (k, entry)
  | .ok _    => .error s!"'{key}' must be an object"
  | .error _ => .ok []

def parseFormal (j : Lean.Json) : Except String FormalStatement := do
  let source := getOptStr j "source"
  let uri    := getOptStr j "uri"
  if source.isNone && uri.isNone then
    throw "formal statement needs 'source' or 'uri'"
  return { language := ← getStr j "language", source, uri }

def parseStatement (j : Lean.Json) : Except String Statement := do
  let formal ← match j.getObjVal? "formal" with
    | .ok f    => some <$> parseFormal f
    | .error _ => pure none
  return { text := ← getStr j "text", formal }

def outcomes : List String := ["verified", "falsified", "partial", "inconclusive"]

def parseArtifact (j : Lean.Json) : Except String ArtifactRef := do
  let hash ← match j.getObjVal? "hash" with
    | .ok h    => some <$> parseDigest h
    | .error _ => pure none
  return { uri := ← getStr j "uri", hash, mediaType := getOptStr j "mediaType" }

def parseEvidence (j : Lean.Json) : Except String EvidenceRecord := do
  let outcome ← getStr j "outcome"
  unless outcomes.contains outcome do
    throw s!"invalid evidence outcome '{outcome}' (must be one of {outcomes})"
  let artifact ← match j.getObjVal? "artifact" with
    | .ok a    => some <$> parseArtifact a
    | .error _ => pure none
  return {
    method     := ← getStr j "method"
    verifier   := ← getStr j "verifier"
    tool       := getOptStr j "tool"
    outcome
    date       := ← getStr j "date"
    scriptHash := getOptStr j "scriptHash"
    artifact
    notes      := getOptStr j "notes"
  }

def parseProperty (j : Lean.Json) : Except String Property := do
  let id ← getStr j "id"
  let scope ← match j.getObjVal? "scope" with
    | .ok s    => pure s
    | .error _ => throw s!"property '{id}': missing 'scope'"
  let validators ← match scope.getObjVal? "validators" with
    | .ok (.arr a) => a.toList.mapM fun
        | .str s => .ok s
        | _      => .error s!"property '{id}': scope validators must be strings"
    | _ => throw s!"property '{id}': missing 'scope.validators'"
  if validators.isEmpty then
    throw s!"property '{id}': 'scope.validators' must not be empty"
  let statement ← match j.getObjVal? "statement" with
    | .ok s    => (parseStatement s).mapError (s!"property '{id}': {·}")
    | .error _ => throw s!"property '{id}': missing 'statement'"
  let assumptions ← match j.getObjVal? "assumptions" with
    | .ok (.arr a) => a.toList.mapM parseStatement
    | _            => pure []
  let tags := match j.getObjVal? "tags" with
    | .ok (.arr a) => a.toList.filterMap fun | .str s => some s | _ => none
    | _            => []
  let evidence ← match j.getObjVal? "evidence" with
    | .ok (.arr a) => a.mapM (fun e => (parseEvidence e).mapError (s!"property '{id}': {·}"))
    | _            => pure #[]
  return { id, title := getOptStr j "title", scopeValidators := validators,
           statement, assumptions, tags, evidence }

def parseDocument (s : String) : Except String Document := do
  let json ← Lean.Json.parse s
  let schemaUri ← getStr json "$schema"
  let preamble ← match json.getObjVal? "preamble" with
    | .ok p    => pure p
    | .error _ => throw "missing 'preamble'"
  let authors := match preamble.getObjVal? "authors" with
    | .ok (.arr a) => a.toList.filterMap fun | .str s => some s | _ => none
    | _            => []
  let bpJson ← match json.getObjVal? "blueprint" with
    | .ok b    => pure b
    | .error _ => throw "missing 'blueprint'"
  let bpHash ← match bpJson.getObjVal? "hash" with
    | .ok h    => some <$> parseDigest h
    | .error _ => pure none
  let languages ← parseRegistry json "languages"
  let tools ← parseRegistry json "tools"
  let properties ← match json.getObjVal? "properties" with
    | .ok (.arr a) => a.mapM parseProperty
    | .ok _        => throw "'properties' must be an array"
    | .error _     => throw "missing 'properties'"
  if properties.isEmpty then
    throw "'properties' must contain at least one property"
  return {
    schemaUri
    title       := ← getStr preamble "title"
    description := getOptStr preamble "description"
    version     := getOptStr preamble "version"
    authors
    created     := ← getStr preamble "created"
    license     := getOptStr preamble "license"
    blueprint   := { uri := ← getStr bpJson "uri", hash := bpHash }
    languages, tools, properties
  }

/-! ### Blueprint location & binding -/

/-- `true` when the URI carries a scheme other than `file` (e.g. `https://…`). -/
def hasRemoteScheme (uri : String) : Bool :=
  match uri.splitOn "://" with
  | scheme :: _ :: _ =>
    !scheme.isEmpty
      && scheme.data.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.')
      && scheme != "file"
  | _ => false

/-- Resolve a local blueprint URI against the assurance document's directory. -/
def resolveLocalUri (assurancePath uri : String) : String :=
  let path := if uri.startsWith "file://" then uri.drop "file://".length else uri
  if path.startsWith "/" then path
  else
    let dir := (System.FilePath.mk assurancePath).parent.getD ⟨"."⟩
    (dir / path).toString

/-- Find the blueprint validator a scope entry refers to: by `id` first, then
    by exact `title`. Ambiguity and unknown references are errors, per the CIP. -/
def resolveValidator (validators : Array BlueprintValidator) (ref : String) :
    Except String BlueprintValidator :=
  let byId := validators.filter (·.id == some ref)
  if h : byId.size = 1 then .ok byId[0]
  else if byId.size > 1 then
    .error s!"validator id '{ref}' is ambiguous in the blueprint"
  else
    let byTitle := validators.filter (·.title == ref)
    if h : byTitle.size = 1 then .ok byTitle[0]
    else if byTitle.size > 1 then
      .error s!"validator title '{ref}' is ambiguous in the blueprint; \
give validators unique 'id' fields"
    else
      .error s!"no validator with id or title '{ref}' in the blueprint"

/-- Does the formal statement's language resolve to Lean? The registry entry's
    `name` decides, falling back to the raw language key. -/
def isLeanLanguage (doc : Document) (langId : String) : Bool :=
  let name := ((doc.languages.lookup langId).map (·.name)).getD langId
  ["lean", "lean4", "lean 4"].contains name.toLower

/-- The `solve-result` blaster should expect when re-running a property, from
    its recorded `formal-proof` evidence: `verified` → `0` (Valid),
    `falsified` → `1`. Claims with only `partial`/`inconclusive` formal-proof
    evidence are not re-run (`none`). No formal-proof evidence at all means the
    document asserts the statement outright: expect Valid. -/
def expectedSolveResult (p : Property) : Option Nat :=
  match p.evidence.toList.filter (·.method == "formal-proof") with
  | []      => some 0
  | ev :: _ =>
    match ev.outcome with
    | "verified"  => some 0
    | "falsified" => some 1
    | _           => none

/-! ### Hashing -/

private def toHex8 (w : UInt32) : String :=
  let hexChars := "0123456789abcdef".data
  String.mk <| (List.range 8).map fun i =>
    hexChars[((w >>> UInt32.ofNat (28 - 4 * i)) &&& 0xF).toNat]!

/-- Lowercase hex sha256 of raw bytes (`Cryptograph.Sha2`). -/
def sha256Hex (bytes : ByteArray) : String :=
  let hashed := Cryptograph.Sha2.Sha256.hashMessage bytes.toList
  String.join (hashed.toList.map toHex8)

end Internal

open Internal

/-- Namespaces opened around re-run property sources, on top of the code-gen
    prelude (`openDecl`): everything needed to state CEK-execution properties
    against the imported validators. -/
def assuranceOpenDecl : String :=
  openDecl ++ " PlutusCore.UPLC.Utils PlutusCore.UPLC.CekMachine \
PlutusCore.UPLC.Term PlutusCore.UPLC.PlutusScript"

/-!
### `#verify_blueprint` command
-/

/-- `#verify_blueprint Ns "assurance.json" ("plutus.json")?` — import the
blueprint referenced by a CIP blueprint-assurance document into namespace `Ns`
(like `#import_blueprints`), check the binding chain (blueprint hash, validator
references, evidence script hashes), and re-run every property whose formal
statement is inline Lean by handing it to `#blaster`. The optional second path
overrides the document's `blueprint.uri` (required when that URI is remote). -/
syntax (name := verify_blueprint) "#verify_blueprint" ident str (str)? : command

@[command_elab verify_blueprint]
def verifyBlueprintImpl : CommandElab := fun stx => do
  let nsIdent := stx[1]
  let pathLit := stx[2]
  let some assurancePath := pathLit.isStrLit?
    | throwErrorAt pathLit "string literal expected"
  let overridePath : Option String :=
    if stx[3].getNumArgs == 0 then none else stx[3][0].isStrLit?
  let ns := nsIdent.getId

  -- 1. Parse the assurance document.
  let content ← liftM (IO.FS.readFile (System.FilePath.mk assurancePath))
  let doc ← match parseDocument content with
    | .ok d    => pure d
    | .error e => throwError s!"Failed to parse assurance document '{assurancePath}': {e}"

  -- 2. Locate the blueprint.
  let bpPath ← match overridePath with
    | some p => pure p
    | none =>
      if hasRemoteScheme doc.blueprint.uri then
        throwError s!"Assurance document references a remote blueprint \
('{doc.blueprint.uri}'); pass a local copy as a second argument: \
#verify_blueprint {ns} \"{assurancePath}\" \"path/to/plutus.json\""
      else
        pure (resolveLocalUri assurancePath doc.blueprint.uri)

  -- 3. Tamper check against the declared blueprint hash.
  if let some dig := doc.blueprint.hash then
    let alg := dig.alg.toLower
    if alg == "sha256" || alg == "sha-256" then
      let bytes ← liftM (IO.FS.readBinFile (System.FilePath.mk bpPath))
      let actual := sha256Hex bytes
      if actual != dig.digest.toLower then
        throwError s!"Blueprint hash mismatch: assurance document was written \
against sha256 {dig.digest}, but '{bpPath}' hashes to {actual}. The claims may \
not apply to this blueprint."
    else
      logWarning s!"Blueprint hash algorithm '{dig.alg}' is not supported; \
tamper check skipped."

  -- 4. Import the blueprint (same effect as #import_blueprints).
  let blueprint ← elabBlueprintImport ns bpPath

  -- 5./6. Per-property checks and re-runs.
  let mut reran           := 0
  let mut skippedInformal := 0
  let mut skippedLang     := 0
  let mut skippedUri      := 0
  let mut skippedOutcome  := 0

  for p in doc.properties do
    -- Bind scope references to blueprint validators.
    let mut boundValidators : List BlueprintValidator := []
    for ref in p.scopeValidators do
      match resolveValidator blueprint.validators ref with
      | .ok v    => boundValidators := boundValidators ++ [v]
      | .error e => throwError s!"Property '{p.id}': {e}"
    -- Stale-claim detection: evidence scriptHash vs blueprint validator hash.
    for ev in p.evidence do
      if let some sh := ev.scriptHash then
        for v in boundValidators do
          if let some h := v.hash then
            if h.toLower != sh.toLower then
              logWarning s!"Property '{p.id}': evidence ({ev.method}, {ev.date}) \
was produced against script hash {sh}, but blueprint validator '{v.title}' now \
has hash {h} — the claim may be stale."
    -- Re-run the formal statement, if we can.
    match p.statement.formal with
    | none =>
      logInfo s!"Property '{p.id}': natural-language statement only; not re-run."
      skippedInformal := skippedInformal + 1
    | some f =>
      if !isLeanLanguage doc f.language then
        logWarning s!"Property '{p.id}': formal language '{f.language}' is not \
supported for re-verification; skipped."
        skippedLang := skippedLang + 1
      else match f.source with
      | none =>
        logWarning s!"Property '{p.id}': formal statement is only available by \
URI ({f.uri.getD "<missing>"}); inline 'source' is required for re-verification; \
skipped."
        skippedUri := skippedUri + 1
      | some src =>
        match expectedSolveResult p with
        | none =>
          logInfo s!"Property '{p.id}': recorded formal-proof outcome is \
partial/inconclusive; not re-run."
          skippedOutcome := skippedOutcome + 1
        | some n =>
          logInfo s!"Property '{p.id}': re-running with blaster \
(expecting {if n == 0 then "Valid" else "Falsified"})."
          withTempNamespace ns do
            elabCommand (← parseCommand assuranceOpenDecl)
            elabCommand (← parseCommand s!"#blaster (solve-result: {n}) [ {src} ]")
          reran := reran + 1

  -- 7. Summary.
  let skipped := skippedInformal + skippedLang + skippedUri + skippedOutcome
  let plural := if doc.properties.size == 1 then "property" else "properties"
  logInfo s!"Assurance document '{doc.title}': {doc.properties.size} {plural} \
— {reran} re-run with blaster, {skipped} not re-run \
({skippedInformal} natural-language only, {skippedLang} unsupported language, \
{skippedUri} source by URI, {skippedOutcome} partial/inconclusive)."

end PlutusCore.UPLC.BlueprintEncoding.Assurance
