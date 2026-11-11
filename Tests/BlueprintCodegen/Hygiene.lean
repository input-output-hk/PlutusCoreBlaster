import PlutusCore.UPLC.BlueprintEncoding.Assurance

open Lean Elab Command
open PlutusCore.UPLC.BlueprintEncoding
open PlutusCore.UPLC.BlueprintEncoding.Internal
open PlutusCore.Data (Data)
open PlutusCore.IsData (IsData)

namespace Tests.BlueprintCodegen.Hygiene
#import_blueprints Bp "Tests/BlueprintCodegen/fixtures/hygiene.json"

def value : Bp.Consumer :=
  ⟨.I 7, 8, 9, 10, "é", true, .True, ⟨5⟩, .Option, .List, .Integer,
   .ByteString, .Data, .IsData, .Repr, .Unit, .PlutusCore, .True, .False, ._f0⟩

-- Correct positions and wire bytes, not only a round trip between two codecs.
#guard (match IsData.toData value with
  | .Constr 0 (.I 7 :: .I 8 :: .I 9 :: .I 10 :: .B text :: .Constr 1 [] :: _) =>
    text.data.data.map Char.toNat == [0xc3, 0xa9]
  | _ => false)
#guard ((IsData.fromData (IsData.toData value) : Option Bp.Consumer).map (·.b)) == some 8
#guard ((IsData.fromData (IsData.toData value) : Option Bp.Consumer).map (·.text)) == some "é"
#guard ((IsData.fromData (IsData.toData value) : Option Bp.Consumer).map IsData.toData) == some (IsData.toData value)

-- Fields that sanitize to a generated pattern variable must remain positional.
run_cmd do
  let doc ← ofExcept (Json.parse (include_str "fixtures/hygiene.json"))
  let defs ← ofExcept (doc.getObjVal? "definitions")
  let consumer ← ofExcept (defs.getObjVal? "Consumer")
  let fs ← ofExcept (consumer.getObjValAs? (Array Json) "fields")
  for (title, i) in ["_v1", "$v1", "-v1", "some", "none", "Rec"].zipIdx do
    let fs := fs.set! 0 (Json.mkObj [("title", toJson title), ("schema", Json.mkObj [])])
    let c := Json.mkObj [("title", toJson "Rec"), ("dataType", toJson "constructor"),
      ("index", toJson (0 : Nat)), ("fields", toJson (fs.extract 0 2))]
    let bp := Json.mkObj [("preamble", ← ofExcept (doc.getObjVal? "preamble")),
      ("validators", toJson (#[] : Array Json)), ("definitions", Json.mkObj [("Rec", c)])]
    let path ← IO.FS.createTempFile
    try
      path.1.putStr bp.compress
      path.1.flush
      let ns := Name.mkStr `Tests.BlueprintCodegen.Hygiene ("Capture" ++ toString i)
      discard <| elabBlueprintImport ns path.2.toString
      elabCommand (← parseCommand s!"example : (_root_.PlutusCore.IsData.IsData.fromData (.Constr 0 [.I 7, .I 8]) : Option {ns}.Rec).map (fun r => r.b) = some 8 := rfl")
    finally IO.FS.removeFile path.2

-- Named schema types do not capture the native wrapper's Bool/String binders,
-- the imported CEK names, or the result predicate's True/False constructors.
def Bp.script : PlutusCore.UPLC.PlutusScript.PlutusScript :=
  ⟨.PlutusV3, .Program (.Version 1 0 0) (.Lam (.Var 0))⟩
run_cmd do
  emitAppliedWrapper `Tests.BlueprintCodegen.Hygiene.Bp "echoBool" "script" #[⟨.asNative "#boolean", .bool⟩] 100 "E"
  emitAppliedWrapper `Tests.BlueprintCodegen.Hygiene.Bp "echoString" "script" #[⟨.asNative "#string", .string⟩] 100 "E"
  let bp ← ofExcept (Json.parse (include_str "fixtures/applied.json"))
  let validators ← ofExcept (bp.getObjValAs? (Array Json) "validators")
  emitAssuranceFunction `Tests.BlueprintCodegen.Hygiene.Bp "helper"
    (← ofExcept (getStr validators[0]! "compiledCode")) "v3" #[⟨.asNative "#boolean", .bool⟩] ⟨.asNative "#boolean", .bool⟩ 100 "E"

#guard (match Bp.echoBool true with | .Halt (.VCon (.Bool true)) => true | _ => false)
#guard (match Bp.echoString "é" with | .Halt (.VCon (.String "é")) => true | _ => false)
#check (Bp.helper_returns : Bool → Bool → Prop)
end Tests.BlueprintCodegen.Hygiene
