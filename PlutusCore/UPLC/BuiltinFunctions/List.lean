import PlutusCore.List
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.BuiltinFunctions.List

namespace PLC
  open PlutusCore.List
  export PlutusCore.List (
    -- macro_rules chooseList imported implicitly
    mkCons
    headList
    tailList
    nullList
  )
end PLC

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.BuiltinFunctions.Utils

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define chooseList
def chooseList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [listCase, nullCase, CekValue.VCon (Const.ConstList l)]
  | [listCase, nullCase, CekValue.VCon (Const.ConstDataList l)]
  | [listCase, nullCase, CekValue.VCon (Const.ConstPairDataList l)] => some (UPLC.chooseList l nullCase listCase)
  | _ => none

-- Define mkCons
def mkCons (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList xs), CekValue.VCon x] =>
      some (CekValue.VCon (Const.ConstList (PLC.mkCons x xs)))

  | [CekValue.VCon (Const.ConstDataList xs), CekValue.VCon (Const.Data x)] =>
      -- case for ConstDataList
      some (CekValue.VCon (Const.ConstDataList (PLC.mkCons x xs)))

  | [CekValue.VCon (Const.ConstPairDataList xs), CekValue.VCon (Const.PairData p)] =>
      -- case for ConsPairDataList
      some (CekValue.VCon (Const.ConstPairDataList (PLC.mkCons p xs)))
  | _ => none

-- Define headList
def headList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList xs)] =>
      tryCatchSome (PLC.headList xs) (CekValue.VCon)

  | [CekValue.VCon (Const.ConstDataList xs)] =>
      -- case for ConstDataList
      tryCatchSome (PLC.headList xs) (CekValue.VCon ∘ Const.Data)

  | [CekValue.VCon (Const.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
      tryCatchSome (PLC.headList xs) (CekValue.VCon ∘ Const.PairData)

  | _ => none

-- Define tailList
def tailList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList xs)] =>
      tryCatchSome (PLC.tailList xs) (CekValue.VCon ∘ Const.ConstList)

  | [CekValue.VCon (Const.ConstDataList xs)] =>
      -- case for ConstDataList
      tryCatchSome (PLC.tailList xs) (CekValue.VCon ∘ Const.ConstDataList)

  | [CekValue.VCon (Const.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
      tryCatchSome (PLC.tailList xs) (CekValue.VCon ∘ Const.ConstPairDataList)
  | _ => none

-- Define nullList
def nullList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [CekValue.VCon (Const.ConstList xs)]
  | [CekValue.VCon (Const.ConstDataList xs)]
  | [CekValue.VCon (Const.ConstPairDataList xs)] =>
      some (CekValue.VCon (Const.Bool (PLC.nullList xs)))
  | _ => none

-- dropList added in the Bitwise/Batch-7 PR

end PlutusCore.UPLC.BuiltinFunctions.List
