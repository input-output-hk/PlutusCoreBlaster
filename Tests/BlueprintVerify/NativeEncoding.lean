import PlutusCore.UPLC.BlueprintEncoding.Assurance
open Lean Elab Command
open PlutusCore.UPLC.BlueprintEncoding
open PlutusCore.UPLC.BlueprintEncoding.Internal
open PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.Term
open PlutusCore.Data

-- Return the parameter unchanged after applying the raw runtime context.
-- Observing the resulting constant tests the wire representation, not only types.
namespace Wire
def script : PlutusScript := ⟨.PlutusV3, .Program (.Version 1 0 0) (.Lam (.Lam (.Var 1)))⟩
end Wire
run_cmd do
  for (name, enc, ty) in [
      ("dataInteger", ArgEncoding.asData, PlutusType.integer),
      ("nativeInteger", .asNative "#integer", .integer),
      ("nativeBytes", .asNative "#bytes", .bytestring),
      ("nativeList", .asNative "#list", .list .data),
      ("nativePair", .asNative "#pair", .pair .data .data),
      ("nativeBool", .asNative "#boolean", .bool),
      ("nativeString", .asNative "#string", .string),
      ("nativeUnit", .asNative "#unit", .unit)] do
    emitAppliedWrapper `Wire name "script" #[⟨enc, ty⟩, ⟨.asData, .data⟩] 100 "E"

#eval show IO Unit from do
  match Wire.dataInteger 7 (.I 0), Wire.nativeInteger 7 (.I 0) with
  | .Halt (.VCon (.Data (.I 7))), .Halt (.VCon (.Integer 7)) => pure ()
  | _, _ => throw (IO.userError "Data/native integer representation collapsed")
  match Wire.nativeBytes {data := "hi"} (.I 0) with
  | .Halt (.VCon (.ByteString _)) => pure ()
  | _ => throw (IO.userError "native bytes encoded as Data")
  match Wire.nativeList [.I 7] (.I 0), Wire.nativePair (.I 7, .I 8) (.I 0) with
  | .Halt (.VCon (.ConstDataList [.I 7])), .Halt (.VCon (.PairData (.I 7, .I 8))) => pure ()
  | _, _ => throw (IO.userError "native container encoding mismatch")
  match Wire.nativeBool true (.I 0), Wire.nativeString "hi" (.I 0), Wire.nativeUnit () (.I 0) with
  | .Halt (.VCon (.Bool true)), .Halt (.VCon (.String "hi")), .Halt (.VCon .Unit) => pure ()
  | _, _, _ => throw (IO.userError "native primitive encoding mismatch")

-- Raw Flat Data artifacts must consume their complete embedded CBOR payload.
#guard (Applied.decodeValue (.Version 1 0 0) ⟨#[0x4c, 0x01, 0x01, 0x07, 0x00, 0x01]⟩).isOk
#guard !(Applied.decodeValue (.Version 1 0 0) ⟨#[0x4c, 0x01, 0x02, 0x07, 0x00, 0x00, 0x01]⟩).isOk
