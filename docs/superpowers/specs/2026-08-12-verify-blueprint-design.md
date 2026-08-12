# Design: `#verify_blueprint` — CIP-XXXX assurance re-verification

Date: 2026-08-12
Status: implemented autonomously; decisions flagged for Romain's review
Depends on: CIP-57 `#import_blueprints` (this branch), CIP-XXXX "Plutus Blueprint
Assurance Documents" (`~/Documents/GitHub/CIPs`, branch
`cip/extended-blueprints-verification`)

## Goal

1. Finish the CIP-57 blueprint parser on `feat/blueprint-parsing` (fix the two
   stale test expectations left by the positional-field codegen improvement,
   green build).
2. Add a `#verify_blueprint` command that consumes a CIP-XXXX **assurance
   document**, imports the referenced blueprint (same machinery as
   `#import_blueprints`), checks the binding chain (blueprint hash, validator
   references, evidence `scriptHash`), and **re-runs every property** whose
   formal statement is written in Lean by handing it to the `#blaster`
   SMT pipeline.

## Part 1 — finishing the parser

What "unfinished" turned out to mean, in decreasing severity:

1. **plutus-tx blueprints failed to import** (the Acme golden file from the
   `plutus` repo). plutus-tx emits schema shapes Aiken never produces, and the
   emitter crashed or silently dropped types on all of them:
   - *duplicate variant titles* (`Datum` has two constructors both titled
     "Datum") → generated `inductive` with colliding constructor names, a hard
     error. Fix: suffix the constructor index on collision (`Datum_0`,
     `Datum_1`).
   - *untitled constructors* (`DatumPayload`, `Datum2`, `Params`, …) → the
     type was skipped with a warning while other types still referenced it, a
     hard error downstream. Fix: fallback constructor names — `mk` for a
     single untitled variant (a record), `c<index>` otherwise.
   - *untitled two-variant field-less sums* (plutus-tx's `Bool`) → now
     recognized and mapped to Lean `Bool` (the `Data` encodings coincide with
     `IsData Bool`), instead of emitting nothing while references degrade.
   - `emitEnumType` was deleted: enums are the no-field special case of the
     (now fallback-naming) `emitSopType`.
2. **The ctf fixtures had drifted**: `00_hello_world` was recompiled upstream
   (new hash, `msg : ByteArray` instead of `Integer`) and `06_tipjar_v2` now
   has a single `tipjar.tipjar` validator compiled for PlutusV2. `CtfTests`
   expectations were rewritten against what is actually on disk. The multisig
   expectations also predated the positional-field emitter improvement
   (`beneficiary` is a typed `Address` now, not raw `Data`).
3. `.plutus-conformance` (a symlink to a `plutus` checkout, created by CI) was
   missing locally — linked to `~/plutus`.

Additionally, the parser now reads the **optional `id` field** on CIP-57
validator objects (legal today; recommended by the assurance CIP for stable
referencing) and surfaces it in `ValidatorInfo`, and the command body was
refactored into a reusable `elabBlueprintImport ns filepath` so
`#verify_blueprint` shares it.

## Part 2 — `#verify_blueprint`

New module `PlutusCore/UPLC/BlueprintEncoding/Assurance.lean`.

### Syntax

```
#verify_blueprint <Namespace> "path/to/assurance.json"
#verify_blueprint <Namespace> "path/to/assurance.json" "path/to/plutus.json"
```

The optional third argument overrides the blueprint location (needed when
`blueprint.uri` is remote — no network access at elaboration time).

### Pipeline

1. **Parse** the assurance document against the CIP-XXXX meta-schema
   (`$schema`, `preamble{title,authors,created,…}`, `blueprint{uri,hash?}`,
   `languages`/`tools` registries, `properties[]` with
   `id`/`scope.validators[]`/`statement{text,formal?}`/`assumptions`/`evidence[]`).
   Unknown `method` values are opaque (open enum); `outcome` is closed
   (`verified|falsified|partial|inconclusive`).
2. **Resolve the blueprint file**: explicit override argument if given; else
   `blueprint.uri` when it has no URI scheme (or `file://`), resolved
   **relative to the assurance document's directory**; else error asking for
   the override.
3. **Tamper check**: when `blueprint.hash` is present with `alg: "sha256"`,
   sha-256 the blueprint file bytes (`Cryptograph.Sha2`) and compare
   (case-insensitive hex). Mismatch is an **error** (the CIP treats the hash
   as tamper evidence). Unsupported `alg` → warning, check skipped.
4. **Import** the blueprint into `<Namespace>` by calling the shared core of
   `#import_blueprints` (refactored out of the command elab so both commands
   use it).
5. **Bind validator references**: each `scope.validators` entry matches a
   blueprint validator by `id` first, then exact `title`. Zero matches or
   ambiguous matches (duplicate titles) → **error**, per the CIP.
6. **Stale-claim check**: for every evidence record carrying a `scriptHash`,
   compare against the bound validators' blueprint `hash`; mismatch →
   **warning** ("stale claim").
7. **Re-run properties**: for each property
   - no `statement.formal` → info: natural-language only, not re-runnable;
   - `formal.language` resolves (via the `languages` registry name, falling
     back to the raw id) to something other than Lean → warning: unsupported
     language, skipped (UAL will slot in here later);
   - Lean statement with only a `uri` (no inline `source`) → warning, skipped;
   - Lean statement with inline `source` → elaborate
     `#blaster (solve-result: N) [ <source> ]` **inside the target namespace**
     with the standard opens (`Data`, `Integer`, `ByteString`, `IsData`,
     `UPLC.Utils`, `UPLC.CekMachine`, `UPLC.Term`), so sources reference the
     imported validators (`foo_spend.script`) and generated datum/redeemer
     types directly. `N` maps the first `formal-proof` evidence outcome:
     `verified → 0 (Valid expected)`, `falsified → 1`, anything else / no
     evidence → 0. Blaster then reports ✅/❌/⚠️ per property; a claim that no
     longer holds fails the build like any other Lean error.
8. **Summary**: one final info message with counts
   (re-run / natural-language / unsupported-language / uri-only).

### Property-statement contract (v1)

`statement.formal.source` for language *Lean* is a **single Lean term of type
`Prop`**, elaborated in the context described above. Assumptions are conveyed
inside the statement itself (`→`); the document-level `assumptions` list is
informational in v1.

### Testing

`Tests/BlueprintVerify/` with fixture assurance documents pointing at the
in-repo Aiken blueprint (`Tests/test/plutus.json`, all-`todo` placeholder
validators — every handler errors, giving cheap decidable properties):

- happy path: Lean property re-verified by blaster (`✅ Valid`), plus a
  natural-language-only property (info) and an unsupported-language property
  (warning), all under `#guard_msgs`;
- binding failures: unknown validator reference (error), blueprint-hash
  mismatch (error), evidence `scriptHash` mismatch (warning).

CI already provisions z3, so blaster-backed tests run there.

## Decisions to revisit

- Remote `blueprint.uri` / `formal.uri` fetching is out (no elab-time
  network); overrides/inline sources are the workaround.
- Only `method: formal-proof` evidence drives the expected blaster result;
  property-test/audit evidence is surfaced but not re-run (can't re-run Aiken
  from Lean).
- `assumptions` are not auto-prepended as hypotheses.
- No `AssuranceInfo` summary value emitted into the environment yet (unlike
  `BlueprintInfo`); add if introspection is wanted.
