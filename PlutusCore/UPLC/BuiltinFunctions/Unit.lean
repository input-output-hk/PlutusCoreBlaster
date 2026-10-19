import PlutusCore.Unit
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.BuiltinFunctions.Unit

namespace PLC
  open PlutusCore.Unit
  export PlutusCore.Unit (
    chooseUnit
  )
end PLC

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue

-- Define chooseUnit
def chooseUnit (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [v, CekValue.VCon Const.Unit] => some (PLC.chooseUnit () v)
  | _ => none


end PlutusCore.UPLC.BuiltinFunctions.Unit
