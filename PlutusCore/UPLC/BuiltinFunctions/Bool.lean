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

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define ifThenElse
def ifThenElse (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [caseFalse, caseTrue, CekValue.VCon (Const.Bool b)] =>
        some (PLC.ifThenElse b caseTrue caseFalse)
  | _ => none

end PlutusCore.UPLC.CekValue
