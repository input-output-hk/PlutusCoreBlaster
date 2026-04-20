import PlutusCore.Array
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.Array

namespace PLC
  open PlutusCore.Array
  export PlutusCore.Array (lengthOfArray listToArray indexArray)
end PLC

open PlutusCore.Array
open PlutusCore.UPLC.Term
open CekValue

def lengthOfArray (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstArray a)] => some (.VCon (.Integer (PLC.lengthOfArray a)))
  | _                       => none

def listToArray (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList l)]         =>               l |> PLC.listToArray |> .ConstArray |> .VCon |> some
  | [.VCon (.ConstDataList l)]     => .Data     <$> l |> PLC.listToArray |> .ConstArray |> .VCon |> some
  | [.VCon (.ConstPairDataList l)] => .PairData <$> l |> PLC.listToArray |> .ConstArray |> .VCon |> some
  | _                              => none

def indexArray (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.Integer i), .VCon (.ConstArray a)] =>
      match i with
      | .ofNat   n => .VCon <$> PLC.indexArray a n
      | .negSucc _ => none
  | _ => none

end PlutusCore.UPLC.Array
