import PlutusCore.Trace
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue
namespace PLC
  open PlutusCore.Trace
  export PlutusCore.Trace (
    trace
  )
end PLC
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue

-- Define trace
def trace (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.String s), v] => some (PLC.trace s v)
  | _ => none

end PlutusCore.UPLC.CekValue
