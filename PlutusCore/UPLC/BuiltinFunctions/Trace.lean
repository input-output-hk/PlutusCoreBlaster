import PlutusCore.Trace
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.BuiltinFunctions.Trace

namespace PLC
  open PlutusCore.Trace
  export PlutusCore.Trace (
    trace
  )
end PLC

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define trace
def trace (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [v, CekValue.VCon (Const.String s)] => some (PLC.trace s v)
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.Trace
