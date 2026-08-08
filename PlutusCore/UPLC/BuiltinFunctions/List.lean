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

/-- Whether two constants have the same outer shape (constructor, and
    recursively the shape of their elements for `Pair`/`ConstList`), ignoring
    the actual values. Used by `mkCons` to reject consing a wrongly-typed
    element onto a `ConstList`, matching Haskell's builtin type check.

    An empty existing list has no element to compare against, so it's
    accepted regardless of `x`'s shape: `Const.ConstList` doesn't retain the
    list's declared element type once it's empty (that's only known during
    decoding), so this check can't be made complete for that case without a
    representation change. -/
private def sameShape : Const → Const → Bool
  | .Integer _, .Integer _                             => true
  | .ByteString _, .ByteString _                        => true
  | .String _, .String _                                => true
  | .Unit, .Unit                                        => true
  | .Bool _, .Bool _                                    => true
  | .Data _, .Data _                                    => true
  | .PairData _, .PairData _                            => true
  | .ConstDataList _, .ConstDataList _                  => true
  | .ConstPairDataList _, .ConstPairDataList _          => true
  | .Bls12_381_G1_element _, .Bls12_381_G1_element _    => true
  | .Bls12_381_G2_element _, .Bls12_381_G2_element _    => true
  | .Bls12_381_MlResult _, .Bls12_381_MlResult _        => true
  | .Pair (a1, b1), .Pair (a2, b2)                      => sameShape a1 a2 && sameShape b1 b2
  | .ConstList (x :: _), .ConstList (y :: _)            => sameShape x y
  | .ConstList _, .ConstList _                          => true
  | _, _ => false

-- Define chooseList
def chooseList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [listCase, nullCase, .VCon (.ConstList l)]
  | [listCase, nullCase, .VCon (.ConstDataList l)]
  | [listCase, nullCase, .VCon (.ConstPairDataList l)] => some (UPLC.chooseList l nullCase listCase)
  | _ => none

-- Define mkCons
def mkCons (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs), .VCon x] =>
      match xs.head? with
      | some h => if sameShape x h then some (.VCon (.ConstList (PLC.mkCons x xs))) else none
      | none => some (.VCon (.ConstList (PLC.mkCons x xs)))

  | [.VCon (.ConstDataList xs), .VCon (.Data x)] =>
      -- case for ConstDataList
      some (.VCon (.ConstDataList (PLC.mkCons x xs)))

  | [.VCon (.ConstPairDataList xs), .VCon (.PairData p)] =>
      -- case for ConsPairDataList
      some (.VCon (.ConstPairDataList (PLC.mkCons p xs)))
  | _ => none

-- Define headList
def headList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs)] =>
         match xs with
         | [] => none
         | x :: _ => some (.VCon x)

  | [.VCon (.ConstDataList xs)] =>
      -- case for ConstDataList
         match xs with
         | [] => none
         | x :: _ => some (.VCon (.Data x))

  | [.VCon (.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
        match xs with
         | [] => none
         | x :: _ => some (.VCon (.PairData x))

  | _ => none

-- Define tailList
def tailList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs)] =>
        match xs with
        | [] => none
        | _ :: tl => some (.VCon (.ConstList tl))

  | [.VCon (.ConstDataList xs)] =>
      -- case for ConstDataList
        match xs with
        | [] => none
        | _ :: tl => some (.VCon (.ConstDataList tl))

  | [.VCon (.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
        match xs with
        | [] => none
        | _ :: tl => some (.VCon (.ConstPairDataList tl))
  | _ => none

-- Define nullList
def nullList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs)]
  | [.VCon (.ConstDataList xs)]
  | [.VCon (.ConstPairDataList xs)] =>
      some (.VCon (.Bool (PLC.nullList xs)))
  | _ => none

-- dropList n xs = xs.drop n (n < 0 treated as 0 via Int.toNat)
-- Eval args (reversed): [list, Integer n]
def dropList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs), .VCon (.Integer n)] =>
      some (.VCon (.ConstList (xs.drop n.toNat)))
  | [.VCon (.ConstDataList xs), .VCon (.Integer n)] =>
      some (.VCon (.ConstDataList (xs.drop n.toNat)))
  | [.VCon (.ConstPairDataList xs), .VCon (.Integer n)] =>
      some (.VCon (.ConstPairDataList (xs.drop n.toNat)))
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.List
