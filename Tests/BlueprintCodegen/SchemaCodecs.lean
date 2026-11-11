import Tests.BlueprintCodegen.Tests

open Lean Elab Command
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.IsData (IsData)
open PlutusCore.UPLC.BlueprintEncoding

namespace Tests.BlueprintCodegen.SchemaCodecs

-- Titles must not determine whether a fieldless constructor resolves to Unit.
-- Both direct and singleton-sum nonzero tags need actual enum declarations.
#import_blueprints TypesBp "Tests/BlueprintCodegen/fixtures/type-plan.json"

#check (TypesBp.ReviewDatum.mk :
  Unit → Unit → TypesBp.Tagged → TypesBp.WrappedTagged → Data → Data → TypesBp.ReviewDatum)

example : IsData.toData TypesBp.Tagged.Tagged = Data.Constr 7 [] := rfl
example : IsData.toData TypesBp.WrappedTagged.Stop = Data.Constr 5 [] := rfl
#guard (IsData.fromData (Data.Constr 7 []) : Option TypesBp.Tagged).isSome
#guard !(IsData.fromData (Data.Constr 0 []) : Option TypesBp.Tagged).isSome
#guard (IsData.fromData (Data.Constr 5 []) : Option TypesBp.WrappedTagged).isSome
#guard !(IsData.fromData (Data.Constr 0 []) : Option TypesBp.WrappedTagged).isSome

def datum : TypesBp.ReviewDatum :=
  ⟨(), (), .Tagged, .Stop, .I 42, .B { data := "raw" }⟩

example : IsData.fromData (IsData.toData datum) = some datum := rfl

run_cmd do
  let bp ← ofExcept (Internal.parseBlueprint
    (include_str "fixtures/type-plan.json"))
  let names := bp.namedTypes.map (·.1)
  unless names.length == 3 && names.contains "Tagged" &&
      names.contains "WrappedTagged" && names.contains "ReviewDatum" do
    throwError "declaration plan includes a unit, unsupported sum, or recursive definition"
  let some v := bp.validators[0]? | throwError "missing test validator"
  let rawRedeemer := match v.redeemer with
    | some s => match s.ptype with | .data => true | _ => false
    | none => false
  unless rawRedeemer do
    throwError "recursive redeemer still references an un-emitted type"
  unless (match v.parameters[0]!.ptype with | .data => true | _ => false) do
    throwError "a type depending on a recursive definition still has a named reference"
  for kind in ["#void"] do
    let schema := Json.mkObj [("dataType", toJson kind)]
    if (Internal.parseFunctionWire schema).isOk then
      throwError "accepted unsupported builtin {kind}"
    let invalidBlueprint := Json.mkObj [
      ("preamble", Json.mkObj [("title", toJson "invalid"), ("version", toJson "1"), ("plutusVersion", toJson "v3")]),
      ("validators", toJson [Json.mkObj [("title", toJson "invalid"),
        ("arguments", toJson [Json.mkObj [("encoding", toJson "asData"), ("schema", schema)]])]])]
    if (Internal.parseBlueprint invalidBlueprint.compress).isOk then
      throwError "accepted #void in a legacy argument"

-- Repeated schema titles must preserve two different types, including their refs.
-- Tokens declared by an importing library must not break generated field names.
syntax "review_token" : term
#import_blueprints ReviewBp "Tests/BlueprintCodegen/fixtures/review.json"
#check (ReviewBp.Review.mk : ReviewBp.Option_Int → ReviewBp.Option_ByteArray →
  PlutusCore.Integer.Integer → ReviewBp.Review)
example : IsData.toData (ReviewBp.Review.mk (.Some 7) (.Some { data := "a" }) 9) =
    .Constr 0 [.Constr 0 [.I 7], .Constr 0 [.B { data := "a" }], .I 9] := rfl
#guard ((IsData.fromData (.Constr 0 [.Constr 0 [.I 7], .Constr 0 [.B { data := "a" }], .I 9]) :
  Option ReviewBp.Review).map (·.Type)) == some 9

run_cmd do
  let blueprint ← ofExcept (Json.parse (include_str "fixtures/review.json"))
  let defs ← ofExcept (blueprint.getObjVal? "definitions")
  let option ← ofExcept (defs.getObjVal? "Option$Int")
  let collision := Json.mkObj [("a$b", option), ("a_b", option)]
  let bp ← ofExcept (blueprint.getObj?)
  let invalid := Json.obj (bp.insert "definitions" collision)
  match Internal.parseBlueprint invalid.compress with
  | .error e => unless (e.splitOn "a$b").length > 1 && (e.splitOn "a_b").length > 1 do
      throwError "collision diagnostic must identify both raw definition keys: {e}"
  | .ok _ => throwError "accepted colliding sanitized definition keys"

def bytes (values : List Nat) : ByteString :=
  { data := String.mk (values.map Char.ofNat) }

def byteValues (d : Data) : List Nat :=
  match d with | .B b => b.data.data.map Char.toNat | _ => []

-- Check actual wire bytes, rather than only a mutually incorrect round-trip.
#guard byteValues (IsData.toData "é") == [0xc3, 0xa9]
#guard byteValues (IsData.toData "€") == [0xe2, 0x82, 0xac]
#guard byteValues (IsData.toData "😀") == [0xf0, 0x9f, 0x98, 0x80]
#guard (IsData.fromData (.B (bytes [0xc3, 0xa9])) : Option String) == some "é"
#guard (IsData.fromData (IsData.toData "Aé€😀") : Option String) == some "Aé€😀"

-- Invalid UTF-8 and non-byte character values must fail decoding.
#guard (IsData.fromData (.B (bytes [0xff])) : Option String).isNone
#guard (IsData.fromData (.B (bytes [0xc3])) : Option String).isNone
#guard (IsData.fromData (.B (bytes [0xc0, 0xaf])) : Option String).isNone
#guard (IsData.fromData (.B (bytes [0xed, 0xa0, 0x80])) : Option String).isNone
#guard (IsData.fromData (.B (bytes [0x100])) : Option String).isNone
#guard (IsData.fromData (.I 0) : Option String).isNone
-- The raw byte domain remains available, including invalid UTF-8.
#guard (IsData.fromData (.B (bytes [0xff])) : Option ByteString) == some (bytes [0xff])

-- Generated field codecs must use the same UTF-8 convention, including lists.
#guard (match IsData.toData (StrBp.StrDatum.mk "é€") with
  | .Constr 0 [b] => byteValues b == [0xc3, 0xa9, 0xe2, 0x82, 0xac]
  | _ => false)
#guard ((IsData.fromData (.Constr 0 [.B (bytes [0xc3, 0xa9])]) : Option StrBp.StrDatum).map (·.label)) == some "é"
#guard (IsData.fromData (.Constr 0 [.B (bytes [0xff])]) : Option StrBp.StrDatum).isNone
#guard (match IsData.toData (StrBp.StrList.mk ["é", "€"]) with
  | .Constr 0 [.List [a, b]] => byteValues a == [0xc3, 0xa9] && byteValues b == [0xe2, 0x82, 0xac]
  | _ => false)
#guard ((IsData.fromData (.Constr 0 [.List [.B (bytes [0xc3, 0xa9])]]) : Option StrBp.StrList).map (·.labels)) == some ["é"]
#guard (IsData.fromData (.Constr 0 [.List [.B (bytes [0xff])]]) : Option StrBp.StrList).isNone

end Tests.BlueprintCodegen.SchemaCodecs
