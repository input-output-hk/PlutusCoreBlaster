import PlutusCore.UPLC.BlueprintEncoding.Assurance

/-!
Tests for `#verify_blueprint` — CIP blueprint-assurance re-verification.

The fixtures reference the all-`todo` Aiken placeholder blueprint
(`Tests/test/plutus.json`), whose every handler errors: "the validator rejects
everything" is a real formal property blaster can re-verify.
-/

namespace Tests.BlueprintVerify

#verify_blueprint VerifyDemo "Tests/BlueprintVerify/fixtures/assurance.json"

end Tests.BlueprintVerify
