import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.PlutusScript

/-!
Regression tests for `#import_blueprints` datum/redeemer type codegen and for
the applied-validator wrapper driven by the `arguments`/`budget` validator
fields. The type-codegen fixtures carry no `compiledCode`, so only the
type/`IsData` generation runs for those.
-/

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.IsData (IsData)
open PlutusCore.UPLC.Term (Term Const)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram State)

namespace Tests.BlueprintCodegen

-- ---------------------------------------------------------------------------
-- #2  map fields must encode to `Data.Map`, not `Data.List` of `Constr`
-- ---------------------------------------------------------------------------
#import_blueprints MapBp "Tests/BlueprintCodegen/fixtures/map.json"

/-- info: MapBp.MapDatum.mk (prices : List (ByteString × Integer)) : MapBp.MapDatum -/
#guard_msgs in
#check MapBp.MapDatum.mk

/-- info: Data.Constr (Int.ofNat 0) [Data.Map [(Data.B { data := "a" }, Data.I (Int.ofNat 1))]] -/
#guard_msgs in
#eval (IsData.toData ({ prices := [({ data := "a" }, (1 : Integer))] } : MapBp.MapDatum))

/-- info: some { prices := [(#61, 1)] } -/
#guard_msgs in
#eval (IsData.fromData (Data.Constr 0 [Data.Map [(Data.B { data := "a" }, Data.I 1)]])
        : Option MapBp.MapDatum)

-- ---------------------------------------------------------------------------
-- #1  string fields must produce compiling code (IsData String)
-- ---------------------------------------------------------------------------
#import_blueprints StrBp "Tests/BlueprintCodegen/fixtures/string.json"

/-- info: StrBp.StrDatum.mk (label : String) : StrBp.StrDatum -/
#guard_msgs in
#check StrBp.StrDatum.mk

/-- info: some { label := "hi" } -/
#guard_msgs in
#eval (IsData.fromData (IsData.toData ({ label := "hi" } : StrBp.StrDatum))
        : Option StrBp.StrDatum)

-- ---------------------------------------------------------------------------
-- #4  keyword / digit-leading field names must be escaped
-- ---------------------------------------------------------------------------
#import_blueprints KwBp "Tests/BlueprintCodegen/fixtures/keyword.json"

/-- info: KwBp.KwDatum.mk («end» type : Integer) : KwBp.KwDatum -/
#guard_msgs in
#check KwBp.KwDatum.mk

-- ---------------------------------------------------------------------------
-- sum-of-products: anyOf with fielded constructors → a real inductive
-- ---------------------------------------------------------------------------
#import_blueprints SopBp "Tests/BlueprintCodegen/fixtures/sop.json"

/-- info: SopBp.Credential.VerificationKey (_f0 : Integer) : SopBp.Credential -/
#guard_msgs in
#check SopBp.Credential.VerificationKey

/-- info: Data.Constr (Int.ofNat 1) [Data.I (Int.ofNat 7)] -/
#guard_msgs in
#eval IsData.toData (SopBp.Credential.Script 7)

/-- info: some (SopBp.Credential.Script 7) -/
#guard_msgs in
#eval (IsData.fromData (Data.Constr 1 [Data.I 7]) : Option SopBp.Credential)

-- ---------------------------------------------------------------------------
-- nested definitions: a record referencing a sum type and a nested record,
-- emitted dependencies-first so every field gets a real Lean type.
-- ---------------------------------------------------------------------------
#import_blueprints NestBp "Tests/BlueprintCodegen/fixtures/nested.json"

/-- info: NestBp.Vault.mk (owner : NestBp.Credential) (assets : List NestBp.Asset) : NestBp.Vault -/
#guard_msgs in
#check NestBp.Vault.mk

/-- info: some { owner := NestBp.Credential.Script #6b, assets := [{ name := #6e, amount := 5 }] } -/
#guard_msgs in
#eval (IsData.fromData (IsData.toData
        (NestBp.Vault.mk (NestBp.Credential.Script { data := "k" }) [NestBp.Asset.mk { data := "n" } 5]))
      : Option NestBp.Vault)

-- ---------------------------------------------------------------------------
-- pair fields encode via Data.Constr 0 [a, b] and recurse through both sides
-- ---------------------------------------------------------------------------
#import_blueprints PairBp "Tests/BlueprintCodegen/fixtures/pair.json"

/-- info: Data.Constr (Int.ofNat 0) [Data.Constr (Int.ofNat 0) [Data.B { data := "a" }, Data.I (Int.ofNat 9)]] -/
#guard_msgs in
#eval IsData.toData ({ pt := ({ data := "a" }, (9 : Integer)) } : PairBp.PairDatum)

/-- info: some { pt := (#61, 9) } -/
#guard_msgs in
#eval (IsData.fromData (Data.Constr 0 [Data.Constr 0 [Data.B { data := "a" }, Data.I 9]])
        : Option PairBp.PairDatum)

-- ---------------------------------------------------------------------------
-- Applied-validator wrappers: the `arguments` + `budget` validator fields.
--
-- The fixture has six validators sharing one compiled program:
--   applied.data      asData Data,                  steps 2500  → wrapper
--   applied.typed     asData Params + asData Data,   steps 1234  → wrapper
--   applied.scott     asScott Params,                steps 2500  → skipped
--   applied.exunits   asData Data,                   exCPU/exMem → skipped
--   applied.nobudget  asData Data,                   no budget   → skipped
--   applied.plain     no `arguments` at all                      → unchanged
-- ---------------------------------------------------------------------------
/-- warning: Blueprint: validator 'applied.scott' declares 'arguments', but no applied-validator wrapper was emitted: an argument declares encoding 'asScott', and this package has no Scott encoder (there is no `IsScott` class here or in `CardanoLedgerApi`), so the applied term would have to be guessed. 'applied_scott' stays bound to the unapplied PlutusScript.
---
warning: Blueprint: validator 'applied.exunits' declares 'arguments', but no applied-validator wrapper was emitted: 'budget' is given as ledger execution units (exCPU 10000000000, exMem 14000000), and there is no conversion from execution units to the CEK step count `cekExecuteProgram` takes. 'applied_exunits' stays bound to the unapplied PlutusScript.
---
warning: Blueprint: validator 'applied.nobudget' declares 'arguments', but no applied-validator wrapper was emitted: the validator declares no 'budget', so there is no CEK step count to run with. 'applied_nobudget' stays bound to the unapplied PlutusScript.
-/
#guard_msgs in
#import_blueprints AppliedBp "Tests/BlueprintCodegen/fixtures/applied.json"

-- With `arguments`, the plain name is the wrapper and the script moves to
-- `_script`; `_hash` keeps the plain prefix.

/-- info: AppliedBp.applied_data (a0 : Data) : State -/
#guard_msgs in
#check AppliedBp.applied_data

/-- info: AppliedBp.applied_data_script : PlutusCore.UPLC.PlutusScript.PlutusScript -/
#guard_msgs in
#check AppliedBp.applied_data_script

/-- info: AppliedBp.applied_data_hash : String -/
#guard_msgs in
#check AppliedBp.applied_data_hash

/-- info: AppliedBp.applied_typed (a0 : AppliedBp.Params) (a1 : Data) : State -/
#guard_msgs in
#check AppliedBp.applied_typed

-- Without a usable `arguments`/`budget` pair the plain name stays the
-- `PlutusScript`, exactly as for a validator that declares neither — no
-- existing project's `<validator>.script` access is disturbed.

/-- info: AppliedBp.applied_scott : PlutusCore.UPLC.PlutusScript.PlutusScript -/
#guard_msgs in
#check AppliedBp.applied_scott

/-- info: AppliedBp.applied_exunits : PlutusCore.UPLC.PlutusScript.PlutusScript -/
#guard_msgs in
#check AppliedBp.applied_exunits

/-- info: AppliedBp.applied_nobudget : PlutusCore.UPLC.PlutusScript.PlutusScript -/
#guard_msgs in
#check AppliedBp.applied_nobudget

/-- info: AppliedBp.applied_plain : PlutusCore.UPLC.PlutusScript.PlutusScript -/
#guard_msgs in
#check AppliedBp.applied_plain

-- The wrapper body is definitionally the term a hand-written CEK property
-- writes: argument order, the `.script` projection and the step count all pin.

example (d : Data) : AppliedBp.applied_data d
    = cekExecuteProgram AppliedBp.applied_data_script.script [Term.Const (Const.Data d)] 2500 :=
  rfl

example (p : AppliedBp.Params) (d : Data) : AppliedBp.applied_typed p d
    = cekExecuteProgram AppliedBp.applied_typed_script.script
        [Term.Const (Const.Data (IsData.toData p)), Term.Const (Const.Data d)] 1234 :=
  rfl

end Tests.BlueprintCodegen
