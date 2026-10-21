import Lean

import Blaster.Command.Syntax
import Cryptograph.Sha2
import PlutusCore.UPLC.BlueprintEncoding.Schema
import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.BlueprintEncoding.Applied
import PlutusCore.UPLC.Utils

namespace PlutusCore.UPLC.BlueprintEncoding.Assurance

open Lean Elab Command
open PlutusCore.UPLC.BlueprintEncoding (elabBlueprintImport)
open PlutusCore.UPLC.BlueprintEncoding.Internal
  (getStr getOptStr openDecl parseCommand parseCommands withTempNamespace BlueprintValidator)

/-! ## Blueprint assurance checking

`#verify_blueprint Ns "assurance.json" ["local-plutus.json"]` validates the
bundled CIP meta-schema and cross-references, checks the blueprint digest and
actual script hashes, imports generated types/wrappers, and runs Blaster on each
available Lean/UAL proposition. Historical evidence is reported independently.
Only def/abbrev fragments are accepted; each proposition gets its declared closure
in an isolated elaboration environment. Third-party sources still require an OS
sandbox: Lean elaboration is executable code. Solver success is SMT verification,
not a reconstructed Lean proof. Unsupported sources are explicitly not checked.
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
  /-- Ids of the document's `formalFragments` whose definitions `source`
      needs in scope. Elaborated, dependencies first, immediately before the
      statement itself. -/
  uses     : List String := []
  deriving Repr, Inhabited

/-- A named, importable block of definitions from the document's top-level
    `formalFragments` array. Properties pull fragments in by id through their
    formal statement's `uses` list; fragments pull each other in through
    `imports`. -/
structure FormalFragment where
  id       : String
  /-- Key into the document's `languages` registry, as for a formal statement. -/
  language : String
  /-- Ids of other fragments this one needs in scope. -/
  imports  : List String
  /-- The fragment body: a block of Lean commands (typically `def`s). -/
  source   : String
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
  functionHashes : List (String × Digest) := []
  checkingContextHash : Option Digest := none
  notes      : Option String
  deriving Repr, Inhabited

/-- One property: what is claimed, about which validators, with what evidence. -/
structure Property where
  id              : String
  title           : Option String
  /-- Validator references (blueprint `id`, falling back to `title`). -/
  scopeValidators : List String
  scopeFunctions : List String := []
  statement       : Statement
  assumptions     : List Statement
  tags            : List String
  evidence        : Array EvidenceRecord
  checkingContext : Option String := none
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
  /-- Named blocks of definitions properties can import via `formal.uses`. -/
  fragments   : Array FormalFragment
  properties  : Array Property
  checkingContexts : List (String × ArtifactRef) := []
  functions : List (String × Json) := []
  definitions : Json := Json.mkObj []
  deriving Inhabited

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

/-- A required array-of-strings field; absent means the empty list, a
    non-array or a non-string entry is an error. -/
def getStrList (j : Lean.Json) (key : String) : Except String (List String) :=
  match j.getObjVal? key with
  | .ok (.arr a) => a.toList.mapM fun
      | .str s => .ok s
      | _      => .error s!"'{key}' entries must be strings"
  | .ok _        => .error s!"'{key}' must be an array of strings"
  | .error _     => .ok []

def parseFormal (j : Lean.Json) : Except String FormalStatement := do
  let source := getOptStr j "source"
  let uri    := getOptStr j "uri"
  if source.isNone && uri.isNone then
    throw "formal statement needs 'source' or 'uri'"
  return { language := ← getStr j "language", source, uri, uses := ← getStrList j "uses" }

def parseFragment (j : Lean.Json) : Except String FormalFragment := do
  let id ← (getStr j "id").mapError (s!"formal fragment: {·}")
  let wrap {α} (r : Except String α) : Except String α :=
    r.mapError (s!"formal fragment '{id}': {·}")
  return {
    id
    language := ← wrap (getStr j "language")
    imports  := ← wrap (getStrList j "imports")
    source   := ← wrap (getStr j "source")
  }

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
    functionHashes := ← match j.getObjVal? "functionHashes" with
      | .ok (.obj o) => o.toList.mapM fun (k, v) => do return (k, ← parseDigest v)
      | _ => pure []
    artifact
    checkingContextHash := ← match j.getObjVal? "checkingContextHash" with
      | .ok h => some <$> parseDigest h | _ => pure none
    notes      := getOptStr j "notes"
  }

def parseProperty (j : Lean.Json) : Except String Property := do
  let id ← getStr j "id"
  let scope ← match j.getObjVal? "scope" with
    | .ok s    => pure s
    | .error _ => throw s!"property '{id}': missing 'scope'"
  let validators ← getStrList scope "validators"
  let functions ← getStrList scope "functions"
  if validators.isEmpty && functions.isEmpty then throw "property scope must not be empty"
  if validators.eraseDups.length != validators.length || functions.eraseDups.length != functions.length then
    throw "duplicate property scope target"
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
  return { id, title := getOptStr j "title", scopeValidators := validators, scopeFunctions := functions,
           statement, assumptions, tags, evidence, checkingContext := getOptStr j "checkingContext" }

def parseDocument (s : String) : Except String Document := do
  let json ← Lean.Json.parse s
  AssuranceSchema.validateDocument json
  let schemaUri ← getStr json "$schema"
  unless ["https://cips.cardano.org/cips/cipXXXX/schemas/assurance.json",
          "https://cips.cardano.org/cips/cipXXXX/schemas/assurance-v2.json"].contains schemaUri do
    throw "unsupported assurance schema"
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
  let fragments ← match json.getObjVal? "formalFragments" with
    | .ok (.arr a) => a.mapM parseFragment
    | .ok _        => throw "'formalFragments' must be an array"
    | .error _     => pure #[]
  -- Fragment ids are the key `formal.uses` and `imports` resolve against.
  for i in [0 : fragments.size] do
    for k in [i + 1 : fragments.size] do
      if fragments[i]!.id == fragments[k]!.id then
        throw s!"duplicate formal fragment id '{fragments[i]!.id}'"
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
    languages, tools, fragments, properties
    definitions := (json.getObjVal? "definitions").toOption.getD (Json.mkObj [])
    functions := ← match json.getObjVal? "functions" with
      | .ok (.obj o) => pure o.toList
      | .error _ => pure []
      | _ => throw "functions must be an object"
    checkingContexts := ← match json.getObjVal? "checkingContexts" with
      | .ok (.obj o) => o.toList.mapM fun (key, value) => do return (key, ← parseArtifact value)
      | _ => pure []
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

/-- Does the formal statement's language resolve to something this command can
    elaborate? The registry entry's `name` decides, falling back to the raw
    language key.

    UAL counts. A UAL property body *is* a Lean `Prop` — UAL's own specification
    requires it — written against this package's vocabulary and the
    `CardanoLedgerApi` formalisation. UAL is the annotation envelope (the
    `{-@ … @-}` blocks and the `ONCHAIN` signature grammar); the formal
    statement it carries is Lean, so it elaborates here unchanged. -/
def isLeanLanguage (doc : Document) (langId : String) : Bool := Id.run do
  let some entry := doc.languages.lookup langId | return false
  let name := entry.name
  let n := name.toLower
  return ["lean", "lean4", "lean 4"].contains n
    || ["ual", "universal annotation language"].contains n

private def supportedLanguageVersion (entry : RegistryEntry) : Bool :=
  let ual := ["ual", "universal annotation language"].contains entry.name.toLower
  (if ual then ["0.4", "0.5", "0.6-draft"] else ["4", "4.24.0"]).contains entry.version

/-! ### Formal fragments -/

/-- Depth-first walk of one fragment id. `st` threads `(handled ids, fragments
    in elaboration order)`; `onStack` is the current `imports` chain, innermost
    first, and exists only to catch cycles. -/
private partial def visitFragment (frags : Array FormalFragment) (onStack : List String)
    (st : List String × List FormalFragment) (fid : String) :
    Except String (List String × List FormalFragment) := do
  if st.1.contains fid then return st
  if onStack.contains fid then
    throw s!"formal fragments form an 'imports' cycle: \
{String.intercalate " → " (onStack.reverse ++ [fid])}"
  let some fr := frags.find? (·.id == fid)
    | throw s!"no formal fragment with id '{fid}' in the document's 'formalFragments'"
  let mut st := st
  for dep in fr.imports do
    st ← visitFragment frags (fid :: onStack) st dep
  return (st.1 ++ [fid], st.2 ++ [fr])

/-- The fragments a property's `uses` list needs, in dependency order.

    `handled` holds the ids already dealt with earlier in this command:
    `withTempNamespace` restores the scope stack but deliberately keeps the
    environment, so a fragment's definitions survive into the next property and
    must be elaborated at most once per `#verify_blueprint`.

    A `uses`/`imports` entry naming no fragment is an error, consistent with how
    unresolvable validator references are handled; so is an `imports` cycle. -/
def fragmentOrder (frags : Array FormalFragment) (handled : List String)
    (uses : List String) : Except String (List FormalFragment) := do
  let mut st : List String × List FormalFragment := (handled, [])
  for u in uses do
    st ← visitFragment frags [] st u
  return st.2

/-- Checks not expressible by the meta-schema, including unused fragments. -/
def validateReferences (doc : Document) : Except String Unit := do
  unless doc.functions.isEmpty || doc.schemaUri.endsWith "assurance-v2.json" do
    throw "functions require assurance-v2"
  for p in doc.properties do
    for id in p.scopeFunctions do
      unless (doc.functions.lookup id).isSome do throw "unknown scoped function"
    if let some key := p.checkingContext then
      unless doc.schemaUri.endsWith "assurance-v2.json" do throw "checking contexts require assurance-v2"
      unless (doc.checkingContexts.lookup key).isSome do throw "unknown checking context"

  let mut ids : List String := []
  let checkFormal (f : FormalStatement) : Except String Unit := do
    unless (doc.languages.lookup f.language).isSome do
      throw s!"unknown language registry key '{f.language}'"
    discard <| fragmentOrder doc.fragments [] f.uses
    for id in f.uses do
      let some _fr := doc.fragments.find? (·.id == id) | throw s!"unknown fragment '{id}'"
      pure ()
  for fr in doc.fragments do
    unless (doc.languages.lookup fr.language).isSome do throw s!"unknown fragment language '{fr.language}'"
    discard <| fragmentOrder doc.fragments [] [fr.id]
    for dep in fr.imports do
      let some _parent := doc.fragments.find? (·.id == dep) | throw s!"unknown fragment '{dep}'"
      pure ()
  for p in doc.properties do
    if ids.contains p.id then throw s!"duplicate property id '{p.id}'"
    ids := p.id :: ids
    for st in p.statement :: p.assumptions do
      if let some f := st.formal then checkFormal f
    for ev in p.evidence do
      if let some tool := ev.tool then
        unless (doc.tools.lookup tool).isSome do throw s!"unknown tool registry key '{tool}'"

/-! ### Hashing -/

private def toHex8 (w : UInt32) : String :=
  let hexChars := "0123456789abcdef".data
  String.mk <| (List.range 8).map fun i =>
    hexChars[((w >>> UInt32.ofNat (28 - 4 * i)) &&& 0xF).toNat]!

/-- Lowercase hex sha256 of raw bytes (`Cryptograph.Sha2`). -/
def sha256Hex (bytes : ByteArray) : String :=
  let hashed := Cryptograph.Sha2.Sha256.hashMessage bytes.toList
  String.join (hashed.toList.map toHex8)

/-- File digests are metadata checks, not proof terms. Prefer the platform's
native SHA-256 utility; the pure implementation remains a portable fallback.
Arguments are passed directly, never through a shell. Like Z3, these executables
belong to the trusted, pinned checking environment. -/
def sha256File (path : System.FilePath) : IO String := do
  for (cmd, args) in [("sha256sum", #["--", path.toString]),
                      ("shasum", #["-a", "256", "--", path.toString])] do
    try
      let result ← IO.Process.output { cmd, args }
      let hash := result.stdout.take 64
      if result.exitCode == 0 && hash.length == 64 &&
          hash.data.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) then
        return hash
    catch _ => pure ()
  return sha256Hex (← IO.FS.readBinFile path)

end Internal

open Internal

/-- Digest-bind bytes before interpreting an artifact, including binary Flat terms. -/
def checkedArtifactBytes (parent : String) (a : ArtifactRef) : IO (String × ByteArray) := do
  if hasRemoteScheme a.uri then throw (IO.userError "remote checking artifacts are unsupported")
  let some h := a.hash | throw (IO.userError "checking artifact requires a digest")
  unless ["sha256", "sha-256"].contains h.alg.toLower do throw (IO.userError "unsupported checking digest algorithm")
  let path := resolveLocalUri parent a.uri
  unless (← sha256File path) == h.digest do throw (IO.userError "checking artifact digest mismatch")
  return (path, ← IO.FS.readBinFile path)

def checkedArtifact (parent : String) (a : ArtifactRef) : IO (String × String) := do
  let (path, bytes) ← checkedArtifactBytes parent a
  let some text := String.fromUTF8? bytes | throw (IO.userError "checking document is not UTF-8")
  return (path, text)

/-- Bind a specialized script to every parameter and the exact template AST.
The artifact's bytes determine its ledger hash; structural equality prevents a
different script from being substituted merely by updating that hash. -/
private def checkApplied (contextPath : String) (bp : Json) (id : String) (params : Json)
    : CommandElabM String := do
  let validators ← ofExcept (bp.getObjValAs? (Array Json) "validators")
  let some v := validators.find? (fun v => getOptStr v "id" == some id)
    | throwError "unknown applied validator"
  let version ← ofExcept (getStr (← ofExcept (bp.getObjVal? "preamble")) "plutusVersion")
  let templateCode ← ofExcept (getStr v "compiledCode")
  unless (← ofExcept (PlutusCore.UPLC.BlueprintEncoding.Internal.actualScriptHash version templateCode)) == (← ofExcept (getStr v "hash")) do
    throwError "applied template hash mismatch"
  let .Program uplcVersion template ← ofExcept (PlutusCore.UPLC.ScriptEncoding.Internal.singleCborEncodedScriptFromHex? templateCode)
  let slots := (v.getObjValAs? (Array Json) "parameters").toOption.getD #[]
  let values ← ofExcept (params.getObjValAs? (Array Json) "values")
  unless values.size == slots.size && !values.isEmpty do throwError "applied parameters must cover every parameter"
  let defs := (bp.getObjVal? "definitions").toOption.getD (Json.mkObj [])
  let mut term := template
  for i in [:values.size] do
    let value := values[i]!
    unless getOptStr value "parameter" == some s!"/parameters/{i}" do
      throwError "applied parameter order/reference mismatch"
    let ref ← ofExcept (parseArtifact (← ofExcept (value.getObjVal? "term")))
    let (_, bytes) ← liftM (checkedArtifactBytes contextPath ref)
    let arg ← ofExcept (Applied.decodeValue uplcVersion bytes)
    ofExcept (Applied.validateValue defs (← ofExcept (slots[i]!.getObjVal? "schema")) arg)
    term := .Apply term arg
  let artifact ← ofExcept (parseArtifact (← ofExcept (params.getObjVal? "appliedScript")))
  let (_, bytes) ← liftM (checkedArtifactBytes contextPath artifact)
  let code := Cryptograph.String.uint8ListToHex bytes.toList
  unless (← ofExcept (PlutusCore.UPLC.BlueprintEncoding.Internal.actualScriptHash version code)) == (← ofExcept (getStr params "appliedScriptHash")) do
    throwError "applied script hash mismatch"
  let program ← ofExcept (PlutusCore.UPLC.ScriptEncoding.Internal.singleCborEncodedScriptFromHex? code)
  unless toExpr program == toExpr (PlutusCore.UPLC.Term.Program.Program uplcVersion term) do
    throwError "applied script is not the ordered application of the template"
  return code

private def solverPath : IO String := do
  let r ← IO.Process.output { cmd := "which", args := #["z3"] }
  unless r.exitCode == 0 do throw (IO.userError "z3 is unavailable")
  return r.stdout.trim

/-- Pin the actual loaded modules, including the evaluator, crypto model and
SMT translation, rather than trusting a version label or source checkout. -/
def captureCheckingEnvironment : CommandElabM Json := do
  let env ← getEnv
  let mut modules := []
  for name in env.header.moduleNames do
    let path ← liftM (findOLean name)
    let hash ← liftM (sha256File path)
    modules := modules ++ [(name.toString, Json.str hash)]
  let compiler ← liftM IO.appPath
  let solver ← liftM solverPath
  -- The runner passes the same configured library to --load-dynlib. Pin its
  -- actual bytes as well as the .oleans used for reflection and optimization.
  let native ← match ← liftM (IO.getEnv "ASSURANCE_NATIVE_LIBRARY") with
    | none => pure []
    | some path => pure [("nativeBlasterSha256", Json.str (← liftM (sha256File path)))]
  return Json.mkObj (native ++ [
    ("format", .str "blaster-loaded-environment-v1"),
    ("leanVersion", .str Lean.versionString),
    ("compilerSha256", .str (← liftM (sha256File compiler))),
    ("solverSha256", .str (← liftM (sha256File solver))),
    ("solverOptions", Json.mkObj [("timeoutSeconds", toJson (60 : Nat)), ("maxRecDepth", toJson (100000 : Nat)), ("maxHeartbeats", toJson (0 : Nat))]),
    ("modules", Json.mkObj modules)])

syntax (name := write_checking_environment) "#write_checking_environment" str : command
@[command_elab write_checking_environment]
def writeCheckingEnvironment : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwError "expected environment file"
  let manifest ← captureCheckingEnvironment
  liftM (IO.FS.writeFile path (manifest.pretty ++ "\n"))

private def validateCheckingEnvironment (expected : Json) : CommandElabM Unit := do
  let actual ← captureCheckingEnvironment
  unless expected == actual do
    throwError "checking environment does not match loaded modules, Lean, solver or options"

private def loadContext (assurancePath bpPath : String) (doc : Document) (p : Property)
    : CommandElabM (List (String × String × BudgetInfo) × Option Digest × Json × List (String × String)) := do
  let some key := p.checkingContext | throwError "compiled-interface checking requires a checkingContext"
  let some artifact := doc.checkingContexts.lookup key | throwError "unknown checking context"
  let (path, content) ← liftM (checkedArtifact assurancePath artifact)
  let ctx ← match Json.parse content with | .ok x => pure x | .error e => throwError e
  unless getOptStr ctx "$schema" == some "https://cips.cardano.org/cips/cipXXXX/schemas/checking-context.json" do
    throwError "unsupported checking-context schema"
  match AssuranceSchema.validateDocument ctx with | .ok () => pure () | .error e => throwError e
  unless getOptStr ctx "profile" == some "https://cips.cardano.org/cips/cipXXXX/profiles/uplc-step-check/v1" do
    throwError "unsupported checking profile"
  let execution ← ofExcept (ctx.getObjVal? "execution")
  unless getOptStr execution "acceptance" == some "evaluation" do throwError "ledger-script acceptance is unsupported"
  let b ← ofExcept (execution.getObjVal? "budget")
  unless getOptStr b "kind" == some "cek-steps" do throwError "ledger units are unsupported"
  let steps ← ofExcept (b.getObjValAs? Nat "steps")
  let sem ← ofExcept (getStr execution "semanticsVariant")
  let targets ← ofExcept (ctx.getObjValAs? (Array Json) "targets")
  let mut ids : List String := []
  let mut selections := []
  let mut applications := []
  let bp ← ofExcept (Json.parse (← liftM (IO.FS.readFile bpPath)))
  for t in targets do
    let (id, purpose) ← match getOptStr t "function" with
      | some id => do
        let some f := doc.functions.lookup id | throwError "unknown checking function"
        let h ← ofExcept (t.getObjVal? "functionHash")
        unless h == (← ofExcept (f.getObjVal? "hash")) do throwError "checking function hash mismatch"
        let iface ← ofExcept (t.getObjVal? "functionInterface")
        for key in ["serialization", "plutusVersion", "arguments", "result"] do
          unless (← ofExcept (iface.getObjVal? key)) == (← ofExcept (f.getObjVal? key)) do
            throwError "checking function interface mismatch: {key}"
        unless (iface.getObjVal? "definitions").toOption.getD (Json.mkObj []) == doc.definitions do
          throwError "checking function definitions mismatch"
        pure (id, "function")
      | none => do
        let id ← ofExcept (getStr t "validator")
        let purpose ← ofExcept (getStr t "purpose")
        let params ← ofExcept (t.getObjVal? "parameters")
        match getOptStr params "mode" with
        | some "universal" => pure ()
        | some "applied" => applications := applications ++ [(id, ← checkApplied path bp id params)]
        | _ => throwError "unsupported parameter mode"
        pure (id, purpose)
    if ids.contains id then throwError "duplicate checking target"
    ids := id :: ids
    selections := selections ++ [(id, purpose, BudgetInfo.semanticSteps steps sem)]
  let expected := p.scopeValidators ++ p.scopeFunctions
  unless ids.length == expected.length && ids.all expected.contains &&
      selections.all (fun (id, purpose, _) => if purpose == "function" then p.scopeFunctions.contains id else p.scopeValidators.contains id) do
    throwError "checking targets do not exactly cover property scope"
  let envRef ← ofExcept (parseArtifact (← ofExcept (ctx.getObjVal? "environment")))
  let (_, envText) ← liftM (checkedArtifact path envRef)
  let manifest ← ofExcept (Json.parse envText)
  return (selections, artifact.hash, manifest, applications)

def assuranceOpenDecl : String :=
  openDecl ++ " PlutusCore.UPLC.Utils PlutusCore.UPLC.CekMachine \
PlutusCore.UPLC.Term PlutusCore.UPLC.PlutusScript"

/-!
### `#verify_blueprint` command
-/

/-- Third-party source must still be executed in an OS sandbox. This restriction
keeps fragments definitional and prevents accidental axioms/options/commands. -/
private def checkFragmentCommand (stx : Syntax) : CommandElabM Unit := do
  unless stx.getKind == ``Lean.Parser.Command.declaration do
    throwError "formal fragments may contain only def/abbrev declarations"
  let decl := stx[1]
  unless decl.getKind == ``Lean.Parser.Command.definition || decl.getKind == ``Lean.Parser.Command.abbrev do
    throwError "formal fragments may contain only def/abbrev declarations"

/-- Follow local definitions before simplification to detect disconnected claims.
This is a dependency check, not a proof of semantic relevance. -/
private partial def dependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then dependencies env rest seen
    else
      let next := match env.find? n with
        | some (.defnInfo info) =>
            if env.isImportedConst n then [] else info.value.getUsedConstants.toList
        | _ => []
      dependencies env (next ++ rest) (seen.insert n)

private def checkSource (ns : Name) (validators : List BlueprintValidator)
    (functions : List String) (src : String) : CommandElabM Blaster.Smt.Result := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term src with
    | .ok stx => pure stx
    | .error e => throwError m!"Invalid formal proposition: {e}"
  liftTermElabM do
    let expr ← instantiateMVars (← Term.elabTermAndSynthesize stx (some (mkSort .zero)))
    if expr.hasSorry then throwError "formal proposition contains sorry"
    let used := dependencies (← getEnv) expr.getUsedConstants.toList
    for v in validators do
      let title := PlutusCore.UPLC.BlueprintEncoding.Internal.sanitizeName v.title
      let raw := if v.arguments.isSome && (PlutusCore.UPLC.BlueprintEncoding.Internal.wrapperBlocker
                       (v.arguments.getD #[]) v.budget).isNone then title ++ "_script" else title
      unless used.contains (Name.mkStr ns raw) do
        throwError m!"formal proposition does not depend on scoped validator '{v.id.getD v.title}'"
    for id in functions do
      let raw := PlutusCore.UPLC.BlueprintEncoding.Internal.sanitizeName id ++ "_script"
      unless used.contains (Name.mkStr ns raw) do
        throwError "formal proposition does not depend on scoped function '{id}'"
    unless (← Blaster.Optimize.findLocalAxioms).isEmpty do
      throwError "assurance checking does not accept local axioms"
    for n in expr.getUsedConstants do
      let axioms ← Lean.collectAxioms n
      if axioms.contains ``sorryAx || axioms.contains `Blaster.Tactic.blasterProven then
        throwError m!"formal proposition depends on an admitted declaration: {n}"
    let solver := {(default : Blaster.Optimize.TranslateEnv) with
      optEnv.options.solverOptions := ({ timeout := some 60 } : Blaster.Options.BlasterOptions)}
    let ((result, _), _) ←
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 0, maxRecDepth := 100000 }) do
        Blaster.Smt.Translate.main expr |>.run solver
    return result

syntax (name := verify_blueprint) "#verify_blueprint" ident str (str)? : command

@[command_elab verify_blueprint]
def verifyBlueprintImpl : CommandElab := fun stx => do
  let some assurancePath := stx[2].isStrLit? | throwError "string literal expected"
  let overridePath := if stx[3].getNumArgs == 0 then none else stx[3][0].isStrLit?
  let ns := stx[1].getId
  let content ← liftM (IO.FS.readFile (System.FilePath.mk assurancePath))
  let doc ← match parseDocument content with
    | .ok d => pure d | .error e => throwError m!"Invalid assurance document: {e}"
  match validateReferences doc with
  | .ok () => pure () | .error e => throwError m!"Invalid assurance references: {e}"
  let bpPath ← match overridePath with
    | some p => pure p
    | none =>
      if hasRemoteScheme doc.blueprint.uri then
        throwError "Remote blueprint requires an explicit local copy"
      pure (resolveLocalUri assurancePath doc.blueprint.uri)
  if let some dig := doc.blueprint.hash then
    unless ["sha256", "sha-256"].contains dig.alg.toLower do
      throwError m!"Unsupported blueprint digest algorithm '{dig.alg}': binding is unverified"
    let actual ← liftM (sha256File (System.FilePath.mk bpPath))
    unless actual == dig.digest do throwError m!"Blueprint hash mismatch: expected {dig.digest}, computed {actual}"
  else
    logWarning "Blueprint document binding is unverified (no blueprint.hash)"
  let parsed ← ofExcept (PlutusCore.UPLC.BlueprintEncoding.Internal.parseBlueprint (← liftM (IO.FS.readFile bpPath)))
  if parsed.extended && doc.blueprint.hash.isNone then throwError "compiled-interface checking requires a blueprint digest"
  if parsed.extended && !doc.schemaUri.endsWith "assurance-v2.json" then
    throwError "compiled-interface checking requires assurance-v2"
  for (id, f) in doc.functions do
    if parsed.validators.any (fun v => v.id == some id) then throwError "function/validator id collision"
    let code ← ofExcept (getStr f "compiledCode")
    let some chars := PlutusCore.UPLC.ScriptEncoding.Internal.hexStringToString code.data []
      | throwError "invalid function compiledCode"
    let hash ← ofExcept (parseDigest (← ofExcept (f.getObjVal? "hash")))
    unless hash.alg == "sha256" do throwError "unsupported function digest algorithm"
    let bytes := ByteArray.mk (chars.map (fun c => UInt8.ofNat c.toNat)).toArray
    unless sha256Hex bytes == hash.digest do throwError "function compiledCode hash mismatch"
    unless getOptStr f "serialization" == some "cbor-flat" do throwError "unsupported function serialization"
    discard <| ofExcept (PlutusCore.UPLC.ScriptEncoding.Internal.singleCborEncodedScriptFromHex? code)
    for arg in ← ofExcept (f.getObjValAs? (Array Json) "arguments") do
      discard <| ofExcept (PlutusCore.UPLC.BlueprintEncoding.Internal.parseFunctionWire arg doc.definitions)
    discard <| ofExcept (PlutusCore.UPLC.BlueprintEncoding.Internal.parseFunctionWire (← ofExcept (f.getObjVal? "result")) doc.definitions)
  let blueprint ← if parsed.extended then pure parsed else elabBlueprintImport ns bpPath
  let mut checkedEnvironments : List Json := []
  let mut checked := 0
  let mut skipped := 0
  let mut failed := 0
  -- Each property gets only its declared fragment closure. Definitions from one
  -- property cannot accidentally satisfy undeclared dependencies of the next.
  for p in doc.properties do
    let mut bound : List BlueprintValidator := []
    for ref in p.scopeValidators do
      let v ← match resolveValidator blueprint.validators ref with
        | .ok v => pure v | .error e => throwError m!"Property '{p.id}': {e}"
      if v.compiledCode.isNone then throwError m!"Property '{p.id}': scoped validator has no compiledCode"
      bound := bound ++ [v]
    -- Historical evidence is reported separately. It never determines a fresh verdict.
    for ev in p.evidence do
      for id in p.scopeFunctions do
        let some f := doc.functions.lookup id | throwError "unknown scoped function"
        let expected ← ofExcept (parseDigest (← ofExcept (f.getObjVal? "hash")))
        match ev.functionHashes.lookup id with
        | none => logWarning "historical evidence is unverifiable (missing function hash)"
        | some h => unless h.alg == expected.alg && h.digest == expected.digest do
            logWarning "historical evidence is stale (function changed)"
      for v in bound do
        if let some sh := ev.scriptHash then
          match v.hash with
          | none => logWarning m!"Property '{p.id}': historical evidence is unverifiable (missing script hash)"
          | some h => if h != sh then logWarning m!"Property '{p.id}': historical evidence is stale"
      if let some artifact := ev.artifact then
        if hasRemoteScheme artifact.uri then
          logWarning m!"Property '{p.id}': historical artifact not checked (remote URI); fresh checking is independent"
        else
          let some digest := artifact.hash | throwError "Artifact digest is required"
          unless ["sha256", "sha-256"].contains digest.alg.toLower do
            throwError m!"Unsupported artifact digest algorithm '{digest.alg}'"
          let path := resolveLocalUri assurancePath artifact.uri
          let actual ← liftM (sha256File (System.FilePath.mk path))
          unless actual == digest.digest do throwError m!"Property '{p.id}': artifact digest mismatch"
    match p.statement.formal with
    | none =>
      logInfo m!"Property '{p.id}': not checked (natural-language only)"
      skipped := skipped + 1
    | some f =>
      if !isLeanLanguage doc f.language then
        logWarning m!"Property '{p.id}': not checked (unsupported language '{f.language}')"
        skipped := skipped + 1
      else
        let entry := (doc.languages.lookup f.language).get!
        let ual := ["ual", "universal annotation language"].contains entry.name.toLower
        unless supportedLanguageVersion entry do
          throwError m!"Unsupported formal-language version '{entry.version}'"
        let some src := f.source | do
          logWarning m!"Property '{p.id}': not checked (formal source is only available by URI)"
          skipped := skipped + 1
          continue
        if blueprint.extended then
          unless ual && entry.version == "0.6-draft" do throwError "compiled-interface checking requires UAL 0.6-draft"
        else if p.checkingContext.isSome || (ual && entry.version == "0.6-draft") then
          throwError "checking context requires compiled-interface blueprint"
        if ual && entry.version == "0.5" then
          for v in bound do
            if v.id.isNone then throwError "UAL 0.5 requires stable validator ids"
            match v.budget with
            | some (.semanticSteps ..) => pure ()
            | _ => throwError "UAL 0.5 requires an explicit steps budget and semantics variant"
            if v.arguments.isNone then throwError "UAL 0.5 requires an explicit arguments list"
            if let some why := PlutusCore.UPLC.BlueprintEncoding.Internal.wrapperBlocker
                (v.arguments.getD #[]) v.budget then throwError m!"Property '{p.id}': {why}"
        let fragments ← match fragmentOrder doc.fragments [] f.uses with
          | .ok fs => pure fs | .error e => throwError m!"{e}"
        let (selections, applications) ← if blueprint.extended then do
          let (selected, hash, manifest, applications) ← loadContext assurancePath bpPath doc p
          if !checkedEnvironments.contains manifest then
            validateCheckingEnvironment manifest
            checkedEnvironments := manifest :: checkedEnvironments
          for ev in p.evidence do
            if let some h := ev.checkingContextHash then
              unless (toJson h.alg, toJson h.digest) == ((toJson (hash.get!).alg), (toJson (hash.get!).digest)) do
                logWarning m!"Property '{p.id}': historical evidence is stale (checking context changed)"
          pure (selected, applications)
        else pure ([], [])
        let savedEnv ← getEnv
        let previousErrors := (← get).messages.toList.countP (fun m => m.severity == .error)
        let result ← try
          let scopedBound ← if blueprint.extended then do
            let imported ← elabBlueprintImport ns bpPath (selections.filter (fun (_, purpose, _) => purpose != "function")) applications
            for (id, purpose, budget) in selections do
              if purpose == "function" then
                let some f := doc.functions.lookup id | throwError "unknown function"
                let args ← (← ofExcept (f.getObjValAs? (Array Json) "arguments")).mapM fun a =>
                  ofExcept (PlutusCore.UPLC.BlueprintEncoding.Internal.parseFunctionWire a doc.definitions)
                let result ← ofExcept (PlutusCore.UPLC.BlueprintEncoding.Internal.parseFunctionWire (← ofExcept (f.getObjVal? "result")) doc.definitions)
                let .semanticSteps steps sem := budget | throwError "function requires semantic steps"
                PlutusCore.UPLC.BlueprintEncoding.Internal.emitAssuranceFunction ns id
                  (← ofExcept (getStr f "compiledCode")) (← ofExcept (getStr f "plutusVersion")) args result steps sem
            p.scopeValidators.mapM fun ref => ofExcept (resolveValidator imported.validators ref)
          else pure bound
          withTempNamespace ns do
            elabCommand (← parseCommand assuranceOpenDecl)
            for fr in fragments do
              unless isLeanLanguage doc fr.language do throwError "Unsupported fragment language"
              unless supportedLanguageVersion ((doc.languages.lookup fr.language).get!) do
                throwError "Unsupported fragment language version"
              for command in ← parseCommands s!"formal fragment '{fr.id}'" fr.source do
                checkFragmentCommand command
                elabCommand command
            logInfo m!"Property '{p.id}': checking fresh proposition"
            if (← get).messages.toList.countP (fun m => m.severity == .error) > previousErrors then
              throwError "generated interface or formal fragments failed to elaborate"
            checkSource ns scopedBound p.scopeFunctions src
        finally
          setEnv savedEnv
        checked := checked + 1
        match result with
        | .Valid => logInfo m!"Property '{p.id}': verified (Blaster SMT; no reconstructed Lean proof)"
        | .Falsified _ =>
          logError m!"Property '{p.id}': falsified"
          failed := failed + 1
        | .Undetermined =>
          logError m!"Property '{p.id}': inconclusive"
          failed := failed + 1
  logInfo m!"Assurance '{doc.title}': {checked} checked, {skipped} not checked, {failed} failed/inconclusive"

end PlutusCore.UPLC.BlueprintEncoding.Assurance
