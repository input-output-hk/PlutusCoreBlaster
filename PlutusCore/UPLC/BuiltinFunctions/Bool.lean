import PlutusCore.Bool
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.BuiltinFunctions.Bool

namespace PLC
  open PlutusCore.Bool
  export PlutusCore.Bool (ifThenElse)
end PLC

open PlutusCore.UPLC.Term
open CekValue

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define ifThenElse
def ifThenElse (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [caseFalse, caseTrue, CekValue.VCon (Const.Bool b)] =>
        PLC.ifThenElse b (some caseTrue) (some caseFalse)
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.Bool
