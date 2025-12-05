import PlutusCore.Bool
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue

namespace PLC
  open PlutusCore.Bool
  export PlutusCore.Bool (ifThenElse)
end PLC

open PlutusCore.UPLC.Term
open CekValue

-- Define ifThenElse
def ifThenElse (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Bool b), caseTrue, caseFalse] =>
        some (PLC.ifThenElse b caseTrue caseFalse)
  | _ => none

end PlutusCore.UPLC.CekValue
