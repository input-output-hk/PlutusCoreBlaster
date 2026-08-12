import PlutusCore.UPLC.BlueprintEncoding.Assurance

/-!
Tests for `#verify_blueprint` — CIP blueprint-assurance re-verification.

The fixtures reference the all-`todo` Aiken placeholder blueprint
(`Tests/test/plutus.json`), whose every handler errors: "the validator rejects
everything" is a real formal property blaster can re-verify.
-/

namespace Tests.BlueprintVerify

-- ---------------------------------------------------------------------------
-- Happy path: blueprint hash checked, validators imported, one Lean property
-- re-verified by blaster (✅ Valid), three properties surfaced but not re-run.
-- ---------------------------------------------------------------------------
/--
info: Property 'spend-always-rejects': re-running with blaster (expecting Valid).
---
info: Property 'documented-only': natural-language statement only; not re-run.
---
warning: Property 'ual-property': formal language 'ual' is not supported for re-verification; skipped.
---
warning: Property 'uri-only': formal statement is only available by URI (https://example.com/publish-rejects.lean); inline 'source' is required for re-verification; skipped.
---
info: Assurance document 'Placeholder validator assurance': 4 properties — 1 re-run with blaster, 3 not re-run (1 natural-language only, 1 unsupported language, 1 source by URI, 0 partial/inconclusive).
---
info: ✅ Valid
-/
#guard_msgs in
#verify_blueprint VerifyDemo "Tests/BlueprintVerify/fixtures/assurance.json"

-- The blueprint import side effects are the same as #import_blueprints.
/-- info: VerifyDemo.placeholder_placeholder_spend : PlutusCore.UPLC.PlutusScript.PlutusScript -/
#guard_msgs in
#check VerifyDemo.placeholder_placeholder_spend

/-- info: VerifyDemo.placeholder_placeholder_spend_hash : String -/
#guard_msgs in
#check (VerifyDemo.placeholder_placeholder_spend_hash : String)

-- ---------------------------------------------------------------------------
-- Validator referenced by blueprint `id`; remote blueprint URI overridden by
-- the second argument; stale evidence scriptHash produces a warning.
-- ---------------------------------------------------------------------------
/--
warning: Property 'referenced-by-id': evidence (manual-review, 2026-08-12) was produced against script hash 0000000000000000000000000000000000000000000000000000dead, but blueprint validator 'placeholder.placeholder.spend' now has hash f2388d136606a27c4a531d0040c3e12e07eb95cd5011793c160707dc — the claim may be stale.
---
info: Property 'referenced-by-id': natural-language statement only; not re-run.
---
info: Assurance document 'By-id validator reference': 1 property — 0 re-run with blaster, 1 not re-run (1 natural-language only, 0 unsupported language, 0 source by URI, 0 partial/inconclusive).
-/
#guard_msgs in
#verify_blueprint ById "Tests/BlueprintVerify/fixtures/assurance-by-id.json" "Tests/BlueprintVerify/fixtures/plutus-with-ids.json"

-- ---------------------------------------------------------------------------
-- Remote blueprint URI without a local override is an error.
-- ---------------------------------------------------------------------------
/--
error: Assurance document references a remote blueprint ('https://example.com/placeholder/plutus.json'); pass a local copy as a second argument: #verify_blueprint ByIdNoOverride "Tests/BlueprintVerify/fixtures/assurance-by-id.json" "path/to/plutus.json"
-/
#guard_msgs in
#verify_blueprint ByIdNoOverride "Tests/BlueprintVerify/fixtures/assurance-by-id.json"

-- ---------------------------------------------------------------------------
-- Tampered blueprint: sha256 mismatch aborts before any import.
-- ---------------------------------------------------------------------------
/--
error: Blueprint hash mismatch: assurance document was written against sha256 00000000000000000000000000000000000000000000000000000000000000ff, but 'Tests/BlueprintVerify/fixtures/../../test/plutus.json' hashes to 07a13b1d536a5bfe48feb213efd0caef0776608989c4d7872e1bdea65c246de2. The claims may not apply to this blueprint.
-/
#guard_msgs in
#verify_blueprint Tampered "Tests/BlueprintVerify/fixtures/assurance-badhash.json"

-- ---------------------------------------------------------------------------
-- A scope entry that matches no validator id or title is an error.
-- ---------------------------------------------------------------------------
/--
error: Property 'dangling-scope': no validator with id or title 'no.such.validator' in the blueprint
-/
#guard_msgs in
#verify_blueprint Dangling "Tests/BlueprintVerify/fixtures/assurance-unknown-validator.json"

end Tests.BlueprintVerify
