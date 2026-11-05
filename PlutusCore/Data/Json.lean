import PlutusCore.Data.Basic

/-!
Serializes Plutus Data as detailed-schema JSON with explicit constructor tags.
Encodes byte strings as hexadecimal and preserves integer, list and map contents.
Provides a reusable representation for tools displaying or exporting concrete Data.
-/

namespace PlutusCore.Data

open Lean (Json toJson)

/-- Encode Plutus Data using the detailed JSON schema. -/
partial def toDetailedJson : Data → Json
  | .I n => Json.mkObj [("int", toJson n)]
  | .B bytes => Json.mkObj [("bytes", toJson <| String.join <|
      bytes.data.data.map (fun c => UInt8.toBitVec c.toUInt8 |>.toHex))]
  | .Constr tag fields => Json.mkObj [("constructor", toJson tag), ("fields", toJson (fields.map toDetailedJson))]
  | .List items => Json.mkObj [("list", toJson (items.map toDetailedJson))]
  | .Map pairs => Json.mkObj [("map", toJson (pairs.map fun (k, v) =>
      Json.mkObj [("k", toDetailedJson k), ("v", toDetailedJson v)]))]

end PlutusCore.Data
