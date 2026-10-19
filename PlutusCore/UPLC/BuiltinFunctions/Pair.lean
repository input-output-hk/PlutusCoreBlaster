import PlutusCore.Pair
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.BuiltinFunctions.Pair

namespace PLC
  open PlutusCore.Pair
  export PlutusCore.Pair (
    fstPair
    sndPair
  )
end PLC

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue

-- Define fstPair
def fstPair (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Pair p)] =>
       some (CekValue.VCon (PLC.fstPair p))
  | [CekValue.VCon (Const.PairData p)] =>
       -- case for PairData
       some (CekValue.VCon (Const.Data (PLC.fstPair p)))
  | _ => none

-- Define sndPair
def sndPair (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.Pair p)] =>
       some (CekValue.VCon (PLC.sndPair p))
  | [CekValue.VCon (Const.PairData p)] =>
       -- case for PairData
       some (CekValue.VCon (Const.Data (PLC.sndPair p)))
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.Pair
