import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.PlutusScript

/-!
Regression tests for `#import_blueprints` datum/redeemer type codegen.
Fixtures carry no `compiledCode`, so only the type/`IsData` generation runs.
-/

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.IsData (IsData)

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

end Tests.BlueprintCodegen
