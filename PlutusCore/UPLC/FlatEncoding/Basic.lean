import PlutusCore.ByteString
import PlutusCore.Cbor
import PlutusCore.Data
import PlutusCore.Integer
import PlutusCore.String

import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.FlatEncoding

open PlutusCore.ByteString (ByteString)
open PlutusCore.Cbor (decodeData)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.String (decodeUtf8)

open PlutusCore.UPLC.Term

-- Spec from herein refers to the Formal Specification of the Plutus Core Language
-- found at https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf

namespace Internal

/- Removes padding from the bit sequence. -/
-- Spec C.1.1. Padding
def unpad : List Bool → Option (List Bool)
  | false :: false :: false :: false :: false :: false :: false :: true :: s => .some s
  | false :: false :: false :: false :: false :: false :: true          :: s => .some s
  | false :: false :: false :: false :: false :: true                   :: s => .some s
  | false :: false :: false :: false :: true                            :: s => .some s
  | false :: false :: false :: true                                     :: s => .some s
  | false :: false :: true                                              :: s => .some s
  | false :: true                                                       :: s => .some s
  | true                                                                :: s => .some s
  | _                                                                        => .none

/- Decodes a fixed with natural number. -/
-- Spec C.2.1. Fixed-width natural numbers
def decodeFixedNat : Nat → List Bool → Option (List Bool × Nat)
  | .zero  ,          s => .some (s, 0)
  | .succ p, false :: s => decodeFixedNat p s
  | .succ p, true  :: s => Prod.map id (2 ^ p + ·) <$> decodeFixedNat p s
  | _      , _          => .none

/- Decodes a list. -/
-- Spec C.2.2. Lists
partial def decodeList {α : Type} (f : List Bool → Option (List Bool × α)) : List Bool -> Option (List Bool × List α)
  | false :: s => .some (s, [])
  | true  :: s => do
      let (s' , x) ← f s
      let (s'', l) ← decodeList f s'
      .some (s'', x :: l)
  | _ => .none

/- Decodes a variable width natural number. -/
-- Spec C.2.3. Natural numbers
def decodeNat (s : List Bool) : Option (List Bool × Nat) := do
  let (s' , ks) ← decodeList (decodeFixedNat 7) s
  let (s'', l)  ← decodeFixedNat 7 s'
  let series    := List.mapIdx (λ i ki => ki * 2 ^ (7 * i)) (ks ++ [l])
  .some (s'', List.sum series)

/- Decodes an integer. -/
-- Spec C.2.4. Integers
def decodeInt (s : List Bool) : Option (List Bool × Integer) := do
  let (s', n) ← decodeNat s
  if n % 2 = 0
    then .some (s',              n      / 2)
    else .some (s', - (Int.ofNat n + 1) / 2)

-- Spec C.2.5. Bytestrings
-- D_C^(n)
def decodeChunk : Nat → List Bool → List Char  → Option (List Bool × List Char)
  | .zero  , s, l => .some (s, List.reverse l)
  | .succ p, s, l => do
      let (s', x) ← decodeFixedNat 8 s
      decodeChunk p s' ((Char.ofNat x) :: l)

-- D_C
def decodeChunks (s : List Bool) : Option (List Bool × List Char) := do
  let (s', n) ← decodeFixedNat 8 s
  decodeChunk n s' []

-- D_C*
partial def decodeCStar (s : List Bool) : Option (List Bool × List Char) := do
  let (s', x) ← decodeChunks s
  match x with
  | [] => .some (s', [])
  | x  =>
      let (s'', l) ← decodeCStar s'
      .some (s'', x ++ l)

/- Decodes a Bytestring. -/
def decodeBytestring (s : List Bool) : Option (List Bool × String) := do
  let unpadded ← unpad s
  let (s', r)  ← decodeCStar unpadded
  .some (s', ⟨r⟩)

/- Decodes a unicode string. -/
-- Spec C.2.6. Strings
def decodeUnicode (s : List Bool) : Option (List Bool × String) := do
  let (s', b) ← decodeBytestring s
  let u       ← Except.toOption (decodeUtf8 b)
  .some (s', u)

/- Decodes a Bool value. -/
def decodeBool : List Bool → Option (List Bool × Bool)
  | b :: s => .some (s, b)
  | _      => .none

partial def decodeConstType : List Nat → Option (List Nat × BuiltinType)
  | 0           :: l => .some (l, .AtomicType .TypeInteger)
  | 1           :: l => .some (l, .AtomicType .TypeByteString)
  | 2           :: l => .some (l, .AtomicType .TypeString)
  | 3           :: l => .some (l, .AtomicType .TypeUnit)
  | 4           :: l => .some (l, .AtomicType .TypeBool)
  | 7 :: 5      :: l => do
      let (l', t) ← decodeConstType l
      .some (l', .TypeOperator (.TypeList t))
  -- | 7 :: 12     :: l => sorry -- TODO: implement array for batch 6
  | 7 :: 7 :: 6 :: l => do
      let (l₁, t₁) ← decodeConstType l
      let (l₂, t₂) ← decodeConstType l₁
      .some (l₂, .TypeOperator (.TypePair t₁ t₂))
  | 8           :: l => .some (l, .AtomicType .TypeData)
  | _      => .none

partial def decodeConstValue (s : List Bool) : BuiltinType → Option (List Bool × Const)
  | .AtomicType .TypeInteger        => Prod.map id .Integer                      <$> decodeInt s
  | .AtomicType .TypeByteString     => Prod.map id (.ByteString ∘ ByteString.mk) <$> decodeBytestring s
  | .AtomicType .TypeString         => Prod.map id .String                       <$> decodeUnicode s
  | .AtomicType .TypeUnit           => .some (s, .Unit)
  | .AtomicType .TypeBool           => Prod.map id .Bool                         <$> decodeBool s
  | .AtomicType .TypeData           => do
      let (s', t) ← decodeBytestring s
      let (_ , d) ← decodeData t
      .some (s', .Data d)
  | .TypeOperator (.TypeList t)     =>
       match t with
       | .AtomicType .TypeData =>
             let decodeConstData (xs : List Bool) : Option (List Bool × Data) :=
               match decodeConstValue xs t with
               | some (xs', Const.Data d) => some (xs', d)
               | _ => none -- don't produce anything on type mismatched
             Prod.map id Const.ConstDataList <$> decodeList decodeConstData s
       | .TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)) =>
             let decodeConstPairData (xs : List Bool) : Option (List Bool × (Data × Data)) :=
               match decodeConstValue xs t with
               | some (xs', Const.PairData p) => some (xs', p)
               | _ => none -- don't produce anything on type mismatched
             Prod.map id .ConstPairDataList <$> decodeList decodeConstPairData s
       | _ => Prod.map id Const.ConstList <$> decodeList (flip decodeConstValue t) s -- heterogenous list
  | .TypeOperator (.TypePair t₁ t₂) => do
      let (s₁, c₁) ← decodeConstValue s  t₁
      let (s₂, c₂) ← decodeConstValue s₁ t₂
      match t₁, t₂ with
      | .AtomicType .TypeData, .AtomicType .TypeData =>
          match c₁, c₂ with
          | Const.Data d₁, Const.Data d₂ => some (s₂, Const.PairData (d₁, d₂))
          | _, _ => none
      | _, _ => some (s₂, Const.Pair (c₁, c₂))


/- Decodes a constant. -/
def decodeConst (s : List Bool) : Option (List Bool × Const) := do
  let (s', l)      ← decodeList (decodeFixedNat 4) s
  let (l', t)      ← decodeConstType l
  let _            ← Option.filter (λ () => l' = []) (.some ())
  decodeConstValue s' t

def builtinTable : List (Nat × BuiltinFun) :=
  [
    ( 0, .AddInteger),
    ( 1, .SubtractInteger),
    ( 2, .MultiplyInteger),
    ( 3, .DivideInteger),
    ( 4, .QuotientInteger),
    ( 5, .RemainderInteger),
    ( 6, .ModInteger),
    ( 7, .EqualsInteger),
    ( 8, .LessThanInteger),
    ( 9, .LessThanEqualsInteger),
    (10, .AppendByteString),
    (11, .ConsByteString),
    (12, .SliceByteString),
    (13, .LengthOfByteString),
    (14, .IndexByteString),
    (15, .EqualsByteString),
    (16, .LessThanByteString),
    (17, .LessThanEqualsByteString),
    (18, .Sha2_256),
    (19, .Sha3_256),
    (20, .Blake2b_256),
    (21, .VerifyEd25519Signature),
    (22, .AppendString),
    (23, .EqualsString),
    (24, .EncodeUtf8),
    (25, .DecodeUtf8),
    (26, .IfThenElse),
    (27, .ChooseUnit),
    (28, .Trace),
    (29, .FstPair),
    (30, .SndPair),
    (31, .ChooseList),
    (32, .MkCons),
    (33, .HeadList),
    (34, .TailList),
    (35, .NullList),
    (36, .ChooseData),
    (37, .ConstrData),
    (38, .MapData),
    (39, .ListData),
    (40, .IData),
    (41, .BData),
    (42, .UnConstrData),
    (43, .UnMapData),
    (44, .UnListData),
    (45, .UnIData),
    (46, .UnBData),
    (47, .EqualsData),
    (48, .MkPairData),
    (49, .MkNilData),
    (50, .MkNilPairData),
    (51, .SerializeData),
    (52, .VerifyEcdsaSecp256k1Signature),
    (53, .VerifySchnorrSecp256k1Signature),
    (54, .Bls12_381_G1_add),
    (55, .Bls12_381_G1_neg),
    (56, .Bls12_381_G1_scalarMul),
    (57, .Bls12_381_G1_equal),
    (58, .Bls12_381_G1_compress),
    (59, .Bls12_381_G1_uncompress),
    (60, .Bls12_381_G1_hashToGroup),
    (61, .Bls12_381_G2_add),
    (62, .Bls12_381_G2_neg),
    (63, .Bls12_381_G2_scalarMul),
    (64, .Bls12_381_G2_equal),
    (65, .Bls12_381_G2_compress),
    (66, .Bls12_381_G2_uncompress),
    (67, .Bls12_381_G2_hashToGroup),
    (68, .Bls12_381_millerLoop),
    (69, .Bls12_381_mulMlResult),
    (70, .Bls12_381_finalVerify),
    (71, .Keccak_256),
    (72, .Blake2b_224),
    (73, .IntegerToByteString),
    (74, .ByteStringToInteger),
    (75, .AndByteString),
    (76, .OrByteString),
    (77, .XorByteString),
    (78, .ComplementByteString),
    (79, .ReadBit),
    (80, .WriteBits),
    (81, .ReplicateByte),
    (82, .ShiftByteString),
    (83, .RotateByteString),
    (84, .CountSetBits),
    (85, .FindFirstSetBit),
    (86, .Ripemd_160),
    (87, .ExpModInteger),
    -- (88, .DropList),   -- TODO: implement these for batch 6
    -- (89, .LengthOfArray),
    -- (90, .ListToArray),
    -- (91, .IndexArray),
    -- (92, .Bls12_381_G1_multiScalarMul),
    -- (93, .Bls12_381_G2_multiScalarMul),
    -- (94, .InsertCoin),
    -- (95, .LookupCoin),
    -- (96, .UnionValue),
    -- (97, .ValueContains),
    -- (98, .ValueData),
    -- (99, .UnValueData),
  ]

def decodeBuiltinFun (_v : Version) (s : List Bool) : Option (List Bool × BuiltinFun) := do
  let (s', n)    ← decodeFixedNat 7 s
  let builtinFun ← List.lookup n builtinTable
  .some (s', builtinFun)

/- Decodes a DeBruijn index.
   Note: the name of the variable is arbitrarily chose to be `dbi_X`. -/
def varName (debruijn : Nat) : String := s!"dbi_{debruijn}"

/- Decodes a DeBruijn index and generates a variable name for it. -/
def decodeVar (nextDebruijn : Nat) (s : List Bool) : Option (List Bool × String) := do
  let (s', n) ← decodeNat s
  let _       ← Option.filter (λ () => n > 0) (.some ())
  .some (s', varName (nextDebruijn - n))

/- Decodes a UPLC term. -/
partial def decodeTerm (v : Version) (nextDeBruijn : Nat) : List Bool → Option (List Bool × Term)
  | false :: false :: false :: false :: s => Prod.map id .Var                          <$> decodeVar nextDeBruijn s
  | false :: false :: false :: true  :: s => Prod.map id .Delay                        <$> decodeTerm v nextDeBruijn s
  | false :: false :: true  :: false :: s => Prod.map id (.Lam (varName nextDeBruijn)) <$> decodeTerm v (nextDeBruijn + 1) s
  | false :: false :: true  :: true  :: s => do
      let (s' , t₁) ← decodeTerm v nextDeBruijn s
      let (s'', t₂) ← decodeTerm v nextDeBruijn s'
      .some (s'', .Apply t₁ t₂)
  | false :: true  :: false :: false :: s => Prod.map id .Const   <$> decodeConst s
  | false :: true  :: false :: true  :: s => Prod.map id .Force   <$> decodeTerm v nextDeBruijn s
  | false :: true  :: true  :: false :: s => .some (s, .Error)
  | false :: true  :: true  :: true  :: s => Prod.map id .Builtin <$> decodeBuiltinFun v s
  | true  :: false :: false :: false :: s => do
      let _        ← if v < .Version 1 1 0 then .none else .some ()
      let (s' , i) ← Option.filter (λ (_, i) => i < 2 ^ 64) (decodeNat s)
      let (s'', l) ← decodeList (decodeTerm v nextDeBruijn) s'
      .some (s'', .Constr i l)
  | true  :: false :: false :: true  :: s => do
      let _        ← if v < .Version 1 1 0 then .none else .some ()
      let (s' , u) ← decodeTerm v nextDeBruijn s
      let (s'', l) ← decodeList (decodeTerm v nextDeBruijn) s'
      .some (s'', .Case u l)
  | _ => .none

/- Decodes the Version of the Program. -/
def decodeVersion (s : List Bool) : Option (List Bool × Version) := do
  let (s'  , a) ← decodeNat s
  let (s'' , b) ← decodeNat s'
  let (s''', c) ← decodeNat s''
  .some (s''', .Version a b c)

/- Decodes a Program from a bit sequence. -/
def decodeProgramFromBits (s : List Bool) : Option Program := do
  let (s', version) ← decodeVersion s
  let (r , t      ) ← decodeTerm version 0 s'
  let unpadded      ← unpad r
  let _             ← Option.filter (λ () => unpadded = []) (.some ())
  .some (.Program version t)

def bitSequenceFromHexDigit : Char → Option (List Bool)
  | '0'       => [false, false, false, false]
  | '1'       => [false, false, false,  true]
  | '2'       => [false, false,  true, false]
  | '3'       => [false, false,  true,  true]
  | '4'       => [false,  true, false, false]
  | '5'       => [false,  true, false,  true]
  | '6'       => [false,  true,  true, false]
  | '7'       => [false,  true,  true,  true]
  | '8'       => [ true, false, false, false]
  | '9'       => [ true, false, false,  true]
  | 'a' | 'A' => [ true, false,  true, false]
  | 'b' | 'B' => [ true, false,  true,  true]
  | 'c' | 'C' => [ true,  true, false, false]
  | 'd' | 'D' => [ true,  true, false,  true]
  | 'e' | 'E' => [ true,  true,  true, false]
  | 'f' | 'F' => [ true,  true,  true,  true]
  | _         => .none

/- Generates a bit sequence for a hex string. -/
def bitSequenceFromHexString : List Char → List Bool → Option (List Bool)
  | []           , acc => .some acc
  | h₁ :: h₂ :: t, acc => do
      let b₁ ← bitSequenceFromHexDigit (Char.toLower h₁)
      let b₂ ← bitSequenceFromHexDigit (Char.toLower h₂)
      bitSequenceFromHexString t (acc ++ b₁ ++ b₂)
  | _            , _   => .none

/- Generates a bit sequence for a byte string. -/
def bitSequenceFromByteString : List Char → List Bool → Option (List Bool)
  | []    , acc => .some acc
  | c :: t, acc =>
      let b   := c |> Char.toUInt8 |> UInt8.toBitVec
      let bcc := [b.getLsb 7, b.getLsb 6, b.getLsb 5, b.getLsb 4, b.getLsb 3, b.getLsb 2, b.getLsb 1, b.getLsb 0]
      bitSequenceFromByteString t (acc ++ bcc)

/- Decodes a Program from a hex string. -/
def decodeProgramFromHexString (hexString : String) : Option Program :=
  bitSequenceFromHexString hexString.data [] >>= decodeProgramFromBits

/- Decodes a Program from a byte string. -/
def decodeProgramFromByteString (s : String) : Option Program :=
  bitSequenceFromByteString s.data [] >>= decodeProgramFromBits

end Internal

export Internal
  (
    decodeProgramFromHexString
    decodeProgramFromByteString
  )

end PlutusCore.UPLC.FlatEncoding
