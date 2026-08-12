import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.PlutusScript

/-!
Tests for `#import_blueprints` using real Aiken-compiled blueprints from
the cardano-ctf repository (../cardano-ctf relative to the project root).

Each test case exercises a different aspect of the import:
- hello_world        : single validator, PlutusV2, no parameters
- tipjar_v2          : single validator, PlutusV2, dotted title, enum redeemer
- multisig_treasury  : two validators, PlutusV2, one has an unapplied parameter
-/

namespace PlutusCore.UPLC.BlueprintEncoding.CtfTests

open PlutusCore.UPLC.PlutusScript
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open PlutusCore.IsData (IsData)

-- ---------------------------------------------------------------------------
-- 00_hello_world — single validator, PlutusV2
--
--   title: "hello_world.hello_world"
--   sanitized: hello_world_hello_world
-- ---------------------------------------------------------------------------
#import_blueprints HelloWorld "../cardano-ctf/00_hello_world/plutus.json"

-- The namespace identifier is itself a BlueprintInfo value — evaluate it to
-- get a human-readable summary without printing the raw script bodies.
/-- info: HelloWorld : BlueprintInfo -/
#guard_msgs in
#check HelloWorld

-- Individual PlutusScript and hash are still accessible as flat definitions.
/-- info: HelloWorld.hello_world_hello_world : PlutusScript -/
#guard_msgs in
#check HelloWorld.hello_world_hello_world

/-- info: PlutusCore.UPLC.PlutusScript.PlutusLanguage.PlutusV2 -/
#guard_msgs in
#eval HelloWorld.hello_world_hello_world.lang

/-- info: "f255ff53f95e4c90e36c3fa4ae205e1d447871b356409816a6ad41e0" -/
#guard_msgs in
#eval HelloWorld.hello_world_hello_world_hash

-- ---------------------------------------------------------------------------
-- Generated types — hello_world
--
--   datum:    Unit-like (no fields) → no type emitted
--   redeemer: struct { msg : ByteString }
-- ---------------------------------------------------------------------------

#check (HelloWorld.Redeemer)
#check (HelloWorld.Redeemer.mk : ByteString → HelloWorld.Redeemer)

-- IsData round-trip
/-- info: some { msg := #48656c6c6f2c20576f726c6421 } -/
#guard_msgs in
#eval
  let r : HelloWorld.Redeemer := { msg := { data := "Hello, World!" } }
  (IsData.fromData (IsData.toData r) : Option HelloWorld.Redeemer)

-- ---------------------------------------------------------------------------
-- 06_tipjar_v2 — single validator, PlutusV2, dotted title
--
--   "tipjar.tipjar" → tipjar_tipjar
--
-- No parameters are declared, so no _paramCount definition is emitted.
-- ---------------------------------------------------------------------------
#import_blueprints TipjarV2 "../cardano-ctf/06_tipjar_v2/plutus.json"

/-- info: TipjarV2 : BlueprintInfo -/
#guard_msgs in
#check TipjarV2

/-- info: TipjarV2.tipjar_tipjar : PlutusScript -/
#guard_msgs in
#check TipjarV2.tipjar_tipjar

/-- info: PlutusCore.UPLC.PlutusScript.PlutusLanguage.PlutusV2 -/
#guard_msgs in
#eval TipjarV2.tipjar_tipjar.lang

/-- info: "dce13fe8eb6622ba1281eb7518c106e804a169dfbb08f4fcf8a0bbfd" -/
#guard_msgs in
#eval TipjarV2.tipjar_tipjar_hash

-- ---------------------------------------------------------------------------
-- Generated types — tipjar_v2
--
--   datum:    struct { owner : ByteString; messages : List ByteString }
--   redeemer: enum   { Claim | AddTip }
-- ---------------------------------------------------------------------------

#check (TipjarV2.Datum)
#check (TipjarV2.Datum.mk : ByteString → List ByteString → TipjarV2.Datum)
#check (TipjarV2.Redeemer)
#check (TipjarV2.Redeemer.Claim : TipjarV2.Redeemer)
#check (TipjarV2.Redeemer.AddTip : TipjarV2.Redeemer)

/-- info: some { owner := #616c696365, messages := [#68656c6c6f] } -/
#guard_msgs in
#eval
  let d : TipjarV2.Datum := { owner := { data := "alice" }, messages := [{ data := "hello" }] }
  (IsData.fromData (IsData.toData d) : Option TipjarV2.Datum)

/-- info: some (TipjarV2.Redeemer.AddTip) -/
#guard_msgs in
#eval
  let r := TipjarV2.Redeemer.AddTip
  (IsData.fromData (IsData.toData r) : Option TipjarV2.Redeemer)

-- ---------------------------------------------------------------------------
-- 03_multisig_treasury — two validators, PlutusV2
--
--   "multisig.multisig"   → multisig_multisig   (no parameters)
--   "treasury.treasury"   → treasury_treasury   (1 unapplied parameter: multisigHash)
-- ---------------------------------------------------------------------------
#import_blueprints MultisigTreasury "../cardano-ctf/03_multisig_treasury/plutus.json"

/-- info: MultisigTreasury : BlueprintInfo -/
#guard_msgs in
#check MultisigTreasury

/-- info: MultisigTreasury.multisig_multisig : PlutusScript -/
#guard_msgs in
#check MultisigTreasury.multisig_multisig

/-- info: MultisigTreasury.treasury_treasury : PlutusScript -/
#guard_msgs in
#check MultisigTreasury.treasury_treasury

/-- info: PlutusCore.UPLC.PlutusScript.PlutusLanguage.PlutusV2 -/
#guard_msgs in
#eval MultisigTreasury.multisig_multisig.lang

/-- info: "533c284a2d8c33cac1a75fefebab468ed0ba65a9d21a5beff709e294" -/
#guard_msgs in
#eval MultisigTreasury.multisig_multisig_hash

/-- info: "11632891b99205bb60c97ea26bb8be7e090477adb1714a6a62881d62" -/
#guard_msgs in
#eval MultisigTreasury.treasury_treasury_hash

-- treasury_treasury has one unapplied parameter (multisigHash : ByteArray).
/-- info: MultisigTreasury.treasury_treasury_paramCount : Nat -/
#guard_msgs in
#check MultisigTreasury.treasury_treasury_paramCount

/-- info: 1 -/
#guard_msgs in
#eval MultisigTreasury.treasury_treasury_paramCount

-- The BlueprintInfo also records the parameter count via the parameters array.
/-- info: 1 -/
#guard_msgs in
#eval (MultisigTreasury.validators[1]!.parameters.size)

-- multisig_multisig has no parameters — _paramCount must NOT exist.
-- (Uncommenting the line below should produce an "unknown identifier" error.)
-- #check MultisigTreasury.multisig_multisig_paramCount

-- ---------------------------------------------------------------------------
-- Generated types — multisig_treasury
--
--   datum:    struct { release_value : Integer; beneficiary : Address; … }
--             (Address / Credential / Optional / Referenced are emitted as
--              real Lean types, dependencies first)
--   redeemer: inspect below
-- ---------------------------------------------------------------------------

#check (MultisigTreasury.MultisigDatum)
-- release_value : Integer, beneficiary : Address,
-- required_signers : List ByteString, signed_users : List ByteString
#check (MultisigTreasury.MultisigDatum.mk :
  Integer → MultisigTreasury.Address → List ByteString → List ByteString
  → MultisigTreasury.MultisigDatum)

-- Address itself is a record with typed credential fields.
#check (MultisigTreasury.Address.mk :
  MultisigTreasury.Credential → MultisigTreasury.Optional → MultisigTreasury.Address)

#eval
  let d : MultisigTreasury.MultisigDatum := {
    release_value    := 1000000
    beneficiary      := { payment_credential := .VerificationKeyCredential { data := "pubkeyhash" }
                          stake_credential   := .None }
    required_signers := [{ data := "signer1" }]
    signed_users     := []
  }
  (IsData.fromData (IsData.toData d) : Option MultisigTreasury.MultisigDatum)

end PlutusCore.UPLC.BlueprintEncoding.CtfTests
