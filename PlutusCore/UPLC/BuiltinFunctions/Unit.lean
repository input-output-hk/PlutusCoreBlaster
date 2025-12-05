import PlutusCore.Unit
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue
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
  | [CekValue.VCon Const.Unit, v] => some (PLC.chooseUnit () v)
  | _ => none


end PlutusCore.UPLC.CekValue
