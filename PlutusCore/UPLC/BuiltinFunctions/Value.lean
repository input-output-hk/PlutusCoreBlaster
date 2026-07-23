import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils
import PlutusCore.Value

namespace PlutusCore.UPLC.BuiltinFunctions.Value

namespace PLC
  export PlutusCore.Value
    (insertCoin lookupCoin unionValue valueContains scaleValue valueData unValueData)
end PLC

open PlutusCore.Value (Value)
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.BuiltinFunctions.Utils
open CekValue

-- Builtin args arrive in reverse order (the CEK machine cons-prepends each
-- value as it consumes the next argument), so patterns list the *last*
-- argument first.

/-- `insertCoin (cur : bytestring) (tok : bytestring) (amt : integer) (v : value)`. -/
def insertCoin (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Value v), .VCon (.Integer amt), .VCon (.ByteString tok), .VCon (.ByteString cur)] =>
      tryCatchSome (PLC.insertCoin cur tok amt v) (CekValue.VCon ∘ Const.Value)
  | _ => none

/-- `lookupCoin (cur : bytestring) (tok : bytestring) (v : value) : integer`.
    Always succeeds (returns 0 for missing entries). -/
def lookupCoin (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Value v), .VCon (.ByteString tok), .VCon (.ByteString cur)] =>
      some (.VCon (.Integer (PLC.lookupCoin cur tok v)))
  | _ => none

/-- `unionValue (a : value) (b : value) : value`. -/
def unionValue (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Value b), .VCon (.Value a)] =>
      tryCatchSome (PLC.unionValue a b) (CekValue.VCon ∘ Const.Value)
  | _ => none

/-- `valueContains (a : value) (b : value) : bool`. -/
def valueContains (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Value b), .VCon (.Value a)] =>
      tryCatchSome (PLC.valueContains a b) (CekValue.VCon ∘ Const.Bool)
  | _ => none

/-- `valueData (v : value) : data`. -/
def valueData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Value v)] =>
      tryCatchSome (PLC.valueData v) (CekValue.VCon ∘ Const.Data)
  | _ => none

/-- `unValueData (d : data) : value`. -/
def unValueData (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Data d)] =>
      tryCatchSome (PLC.unValueData d) (CekValue.VCon ∘ Const.Value)
  | _ => none

/-- `scaleValue (c : integer) (v : value) : value`. -/
def scaleValue (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Value v), .VCon (.Integer c)] =>
      tryCatchSome (PLC.scaleValue c v) (CekValue.VCon ∘ Const.Value)
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.Value
