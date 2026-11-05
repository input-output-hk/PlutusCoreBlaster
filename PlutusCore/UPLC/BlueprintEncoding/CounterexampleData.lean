import Blaster.Counterexample
import PlutusCore.Data

namespace PlutusCore.UPLC.BlueprintEncoding.Counterexample
open Blaster.Counterexample
open PlutusCore.ByteString
open PlutusCore.Data

private def hex (s : String) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.mk (s.toList.flatMap fun c => [digits[c.toNat / 16]!, digits[c.toNat % 16]!])

instance : ToCEX ByteString := ⟨fun b =>
  if b.data.toList.all (fun c => c.toNat < 256) then .bytes (hex b.data)
  else .unavailable "ByteString contains a character outside the byte range"⟩

partial def dataValue : Data → Value
  | .I n => .constructor "PlutusCore.Data" "I" [("value", toCEX n)]
  | .B bs => .constructor "PlutusCore.Data" "B" [("value", toCEX bs)]
  | .List xs => .constructor "PlutusCore.Data" "List" [("values", .list (xs.map dataValue))]
  | .Map xs => .constructor "PlutusCore.Data" "Map" [("entries", .list (xs.map fun (k,v) =>
      .constructor "Prod" "Prod.mk" [("fst", dataValue k), ("snd", dataValue v)]))]
  | .Constr n xs => .constructor "PlutusCore.Data" "Constr"
      [("index", toCEX n), ("fields", .list (xs.map dataValue))]

instance : ToCEX Data := ⟨dataValue⟩

end PlutusCore.UPLC.BlueprintEncoding.Counterexample
