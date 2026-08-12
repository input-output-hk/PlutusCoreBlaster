import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.PlutusScript
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.BlueprintEncoding

open PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.Term
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.IsData (IsData)

-- Import validators from the Acme blueprint that lives in the conformance submodule.
-- Each validator with a `compiledCode` field produces:
--   · Acme.<sanitized_title>             : PlutusScript
--   · Acme.<sanitized_title>_hash        : String
--   · Acme.<sanitized_title>_paramCount  : Nat  (only when params > 0)
#import_blueprints Acme ".plutus-conformance/plutus-tx-plugin/test/Blueprint/Acme.golden.json"

-- Both validators must be imported as PlutusScript values.

/-- info: Acme.Acme_Validator__1 : PlutusScript -/
#guard_msgs in
#check Acme.Acme_Validator__1

/-- info: Acme.Acme_Validator__2 : PlutusScript -/
#guard_msgs in
#check Acme.Acme_Validator__2

-- The decoded scripts must carry the language from the preamble (v3 → PlutusV3).

/-- info: PlutusCore.UPLC.PlutusScript.PlutusLanguage.PlutusV3 -/
#guard_msgs in
#eval Acme.Acme_Validator__1.lang

/-- info: PlutusCore.UPLC.PlutusScript.PlutusLanguage.PlutusV3 -/
#guard_msgs in
#eval Acme.Acme_Validator__2.lang

-- Hashes must match the values recorded in the blueprint.

/-- info: "f965222c8aa4bc34c627ed748023560e90ee3b850d846ea3bfd935d8" -/
#guard_msgs in
#eval Acme.Acme_Validator__1_hash

/-- info: "0716bb19b169c780d863085c8bd67c802d9203db831037307629c2ad" -/
#guard_msgs in
#eval Acme.Acme_Validator__2_hash

-- Both validators declare parameters, so _paramCount must be present.

/-- info: Acme.Acme_Validator__1_paramCount : Nat -/
#guard_msgs in
#check Acme.Acme_Validator__1_paramCount

/-- info: 1 -/
#guard_msgs in
#eval Acme.Acme_Validator__1_paramCount

/-- info: Acme.Acme_Validator__2_paramCount : Nat -/
#guard_msgs in
#check Acme.Acme_Validator__2_paramCount

/-- info: 2 -/
#guard_msgs in
#eval Acme.Acme_Validator__2_paramCount

-- ---------------------------------------------------------------------------
-- Generated types — plutus-tx blueprints carry untitled constructors,
-- duplicate variant titles, and Bool-shaped sums; all must map to usable
-- Lean types.
-- ---------------------------------------------------------------------------

-- Datum: two variants both titled "Datum" → disambiguated by constructor index.
#check (Acme.Datum.Datum_0 : Acme.Datum)
#check (Acme.Datum.Datum_1 : Acme.DatumPayload → Acme.Datum)

-- DatumPayload / Datum2: single untitled constructor → `mk`; the untitled
-- two-variant Bool-shaped sum in Datum2's second field maps to Lean `Bool`.
#check (Acme.DatumPayload.mk : Integer → ByteString → Acme.DatumPayload)
#check (Acme.Datum2.mk : Integer → Bool → Acme.Datum2)

-- Params: untitled record over Unit/Bool/Integer/List/Data/ByteArray refs.
#check (Acme.Params.mk :
  Unit → Bool → Integer → List Integer → Data → ByteString → Acme.Params)

-- IsData round-trips through the disambiguated sum and the Bool-shaped field.
/-- info: some (Acme.Datum.Datum_1 (Acme.DatumPayload.mk 7 #78)) -/
#guard_msgs in
#eval (IsData.fromData (IsData.toData (Acme.Datum.Datum_1 (Acme.DatumPayload.mk 7 { data := "x" })))
        : Option Acme.Datum)

/-- info: some (Acme.Datum2.mk 5 true) -/
#guard_msgs in
#eval (IsData.fromData (IsData.toData (Acme.Datum2.mk 5 true)) : Option Acme.Datum2)

-- ---------------------------------------------------------------------------
-- Aiken-generated blueprint (Tests/test/plutus.json)
--
-- Validator titles use dot-separated names ("placeholder.placeholder.mint"),
-- which sanitize to underscore-separated names.
-- None of the validators carry `parameters`, so no _paramCount defs are created.
-- ---------------------------------------------------------------------------
#import_blueprints Placeholder "Tests/test/plutus.json"

/-- info: Placeholder.placeholder_placeholder_mint : PlutusScript -/
#guard_msgs in
#check Placeholder.placeholder_placeholder_mint

/-- info: Placeholder.placeholder_placeholder_spend : PlutusScript -/
#guard_msgs in
#check Placeholder.placeholder_placeholder_spend

/-- info: Placeholder.placeholder_placeholder_withdraw : PlutusScript -/
#guard_msgs in
#check Placeholder.placeholder_placeholder_withdraw

-- All seven validators share the same compiled code and hash.
/-- info: "f2388d136606a27c4a531d0040c3e12e07eb95cd5011793c160707dc" -/
#guard_msgs in
#eval Placeholder.placeholder_placeholder_mint_hash

/-- info: "f2388d136606a27c4a531d0040c3e12e07eb95cd5011793c160707dc" -/
#guard_msgs in
#eval Placeholder.placeholder_placeholder_spend_hash

-- Language is PlutusV3 (from preamble.plutusVersion = "v3").
/-- info: PlutusCore.UPLC.PlutusScript.PlutusLanguage.PlutusV3 -/
#guard_msgs in
#eval Placeholder.placeholder_placeholder_mint.lang

end PlutusCore.UPLC.BlueprintEncoding
