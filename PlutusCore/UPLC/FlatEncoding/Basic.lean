import PlutusCore.ByteString
import PlutusCore.Cbor
import PlutusCore.Data
import PlutusCore.Integer
import PlutusCore.String

import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.FlatEncoding

open PlutusCore.ByteString (ByteString)
open PlutusCore.Cbor (byteArrayToByteString decodeData)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.String (decodeUtf8)

open PlutusCore.UPLC.Term

-- Spec from herein refers to the Formal Specification of the Plutus Core Language
-- found at https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf

namespace Internal

/-- A bit-level cursor into a `ByteArray`. `bytePos` indexes the current byte, and
    `bitPos : Fin 8` is the bit within that byte (MSB-first). The split layout avoids
    mod/div on every bit read — `nextBit` (the default no-skip case) does pure indexing. -/
structure DecodeState where
  input   : ByteArray
  bytePos : Nat
  bitPos  : Fin 8
deriving DecidableEq

/-- Advance the cursor by `n` bits, re-normalising into (bytePos, bitPos). -/
def DecodeState.advance (d : DecodeState) (n : Nat := 1) : DecodeState :=
  let total := d.bitPos.val + n
  { d with
    bytePos := d.bytePos + total / 8,
    bitPos  := ⟨total % 8, Nat.mod_lt _ (by decide)⟩ }

/-- Total number of bits in the input buffer. -/
def DecodeState.totalBits (d : DecodeState) : Nat := 8 * d.input.size

/-- Total bit offset from the start of the input. -/
def DecodeState.absBit (d : DecodeState) : Nat := 8 * d.bytePos + d.bitPos.val

/-- Read the bit at offset `bitPos + skip` (default `skip = 0` does no mod/div).
    Uses `BitVec.getMsbD` so the bit order matches the legacy MSB-first
    `bitSequenceFromBytes` exactly. -/
def DecodeState.nextBit (d : DecodeState) (skip : Nat := 0) : Option Bool :=
  if skip = 0 then
    ((BitVec.getMsbD · d.bitPos.val) ∘ UInt8.toBitVec) <$> d.input[d.bytePos]?
  else
    let total := d.bitPos.val + skip
    ((BitVec.getMsbD · (total % 8)) ∘ UInt8.toBitVec)  <$> d.input[d.bytePos + total / 8]?

@[simp] theorem DecodeState.advance_input (d : DecodeState) (n : Nat) :
    (d.advance n).input = d.input := rfl

/-- Helper for `unpad`: read `k` bits starting at offset `offset`, expecting
    the pattern `0...01` (k-1 zeros then a one). Returns `some ()` on match. -/
private def readPadAt (d : DecodeState) (offset : Nat) : Nat → Option Unit
  | 0     => .none
  | 1     => do
      let b ← d.nextBit offset
      if b then .some () else .none
  | k + 2 => do
      let b ← d.nextBit offset
      if b then .none else readPadAt d (offset + 1) (k + 1)

/- Removes padding from the bit sequence (advances `d` to the next byte boundary). -/
-- Spec C.1.1. Padding
def unpad (d : DecodeState) : Option DecodeState :=
  let n : Nat := 8 - d.bitPos.val
  match readPadAt d 0 n with
  | .some () => .some (d.advance n)
  | .none    => .none

/- Decodes a fixed with natural number. -/
-- Spec C.2.1. Fixed-width natural numbers
def decodeFixedNat : Nat → DecodeState → Option (DecodeState × Nat)
  | 0    , d => .some (d, 0)
  | p + 1, d => do
      let b       ← d.nextBit
      let (d', n) ← decodeFixedNat p d.advance
      .some (d', if b then 2 ^ p + n else n)

/- Decodes a list. -/
-- Spec C.2.2. Lists
partial def decodeList {α : Type} (f : DecodeState → Option (DecodeState × α))
  (d : DecodeState) : Option (DecodeState × List α) := do
    let b ← d.nextBit
    if b then
      let (d' , x) ← f d.advance
      let (d'', l) ← decodeList f d'
      .some (d'', x :: l)
    else
      .some (d.advance, [])

/- Decodes a variable width natural number. -/
-- Spec C.2.3. Natural numbers
def decodeNat (d : DecodeState) : Option (DecodeState × Nat) := do
  let (d' , ks) ← decodeList (decodeFixedNat 7) d
  let (d'', l)  ← decodeFixedNat 7 d'
  let series    := List.mapIdx (λ i ki => ki * 2 ^ (7 * i)) (ks ++ [l])
  .some (d'', List.sum series)

/- Decodes an integer. -/
-- Spec C.2.4. Integers
def decodeInt (d : DecodeState) : Option (DecodeState × Integer) := do
  let (d', n) ← decodeNat d
  if n % 2 = 0
    then .some (d',              n      / 2)
    else .some (d', - (Int.ofNat n + 1) / 2)

-- Spec C.2.5. Bytestrings
-- D_C^(n)
def decodeChunk : Nat → DecodeState → List UInt8 → Option (DecodeState × List UInt8)
  | .zero  , d, l => .some (d, List.reverse l)
  | .succ p, d, l => do
      let (d', x) ← decodeFixedNat 8 d
      decodeChunk p d' (x.toUInt8 :: l)

-- D_C
def decodeChunks (d : DecodeState) : Option (DecodeState × List UInt8) := do
  let (d', n) ← decodeFixedNat 8 d
  decodeChunk n d' []

-- D_C*
partial def decodeCStar (d : DecodeState) : Option (DecodeState × List UInt8) := do
  let (d', x) ← decodeChunks d
  match x with
  | [] => .some (d', [])
  | x  =>
      let (d'', l) ← decodeCStar d'
      .some (d'', x ++ l)

/- Decodes a Bytestring. -/
def decodeBytestring (d : DecodeState) : Option (DecodeState × ByteArray) := do
  let unpadded ← unpad d
  let (d', r)  ← decodeCStar unpadded
  .some (d', r.toByteArray)

/- Decodes a unicode string. -/
-- Spec C.2.6. Strings
def decodeUnicode (d : DecodeState) : Option (DecodeState × String) := do
  let (d', b) ← decodeBytestring d
  let u       ← Except.toOption (decodeUtf8 (byteArrayToByteString b))
  .some (d', u)

/- Decodes a Bool value. -/
def decodeBool (d : DecodeState) : Option (DecodeState × Bool) := do
  let b ← d.nextBit
  .some (d.advance, b)

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

partial def decodeConstValue (d : DecodeState) : BuiltinType → Option (DecodeState × Const)
  | .AtomicType .TypeInteger        => Prod.map id .Integer <$> decodeInt d
  | .AtomicType .TypeByteString     => Prod.map id (.ByteString ∘ byteArrayToByteString) <$> decodeBytestring d
  | .AtomicType .TypeString         => Prod.map id .String <$> decodeUnicode d
  | .AtomicType .TypeUnit           => .some (d, .Unit)
  | .AtomicType .TypeBool           => Prod.map id .Bool <$> decodeBool d
  | .AtomicType .TypeData           => do
      let (d', t) ← decodeBytestring d
      let (_ , da) ← decodeData t
      .some (d', .Data da)
  | .TypeOperator (.TypeList t)     =>
       match t with
       | .AtomicType .TypeData =>
             let decodeConstData (xs : DecodeState) : Option (DecodeState × Data) :=
               match decodeConstValue xs t with
               | some (xs', Const.Data da) => some (xs', da)
               | _                         => none -- don't produce anything on type mismatched
             Prod.map id Const.ConstDataList <$> decodeList decodeConstData d
       | .TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)) =>
             let decodeConstPairData (xs : DecodeState) : Option (DecodeState × (Data × Data)) :=
               match decodeConstValue xs t with
               | some (xs', Const.PairData p) => some (xs', p)
               | _                            => none -- don't produce anything on type mismatched
             Prod.map id .ConstPairDataList <$> decodeList decodeConstPairData d
       | _ =>
             Prod.map id Const.ConstList <$> decodeList (flip decodeConstValue t) d -- heterogenous list
  | .TypeOperator (.TypePair t₁ t₂) => do
      let (d₁, c₁) ← decodeConstValue d  t₁
      let (d₂, c₂) ← decodeConstValue d₁ t₂
      match t₁, t₂ with
      | .AtomicType .TypeData, .AtomicType .TypeData =>
          match c₁, c₂ with
          | Const.Data da₁, Const.Data da₂ => some (d₂, Const.PairData (da₁, da₂))
          | _             , _              => none
      | _                    , _                     =>
          some (d₂, Const.Pair (c₁, c₂))
  | .AtomicType .TypeBls12_381_G1_element -- BLS values are not serializable
  | .AtomicType .TypeBls12_381_G2_element
  | .AtomicType .TypeBls12_381_MlResult   => none

/- Decodes a constant. -/
def decodeConst (d : DecodeState) : Option (DecodeState × Const) := do
  let (d', l) ← decodeList (decodeFixedNat 4) d
  let (l', t) ← decodeConstType l
  let _       ← Option.filter (λ () => l' = []) (.some ())
  decodeConstValue d' t

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
    (88, .DropList),
    -- (89, .LengthOfArray),
    -- (90, .ListToArray),
    -- (91, .IndexArray),
    (92, .Bls12_381_G1_multiScalarMul),
    (93, .Bls12_381_G2_multiScalarMul),
    -- (94, .InsertCoin),
    -- (95, .LookupCoin),
    -- (96, .UnionValue),
    -- (97, .ValueContains),
    -- (98, .ValueData),
    -- (99, .UnValueData),
  ]

def decodeBuiltinFun (_v : Version) (d : DecodeState) : Option (DecodeState × BuiltinFun) := do
  let (d', n)    ← decodeFixedNat 7 d
  let builtinFun ← List.lookup n builtinTable
  .some (d', builtinFun)

/- Display-only binder name for the lambda introduced at nesting level X. -/
def varName (debruijn : Nat) : String := s!"dbi_{debruijn}"

/- Decodes a DeBruijn index.
   Flat encodes 1-based relative indices (index 0 is invalid); `Term.Var`
   uses 0-based indices (0 = innermost binder), so we subtract 1. -/
def decodeVar (nextDebruijn : Nat) (d : DecodeState) : Option (DecodeState × Nat) := do
  let (d', n) ← decodeNat d
  let _       ← Option.filter (λ () => n > 0) (.some ())
  .some (d', n - 1)

/- Decodes a UPLC term. -/
partial def decodeTerm (v : Version) (nextDeBruijn : Nat) (d : DecodeState) : Option (DecodeState × Term) := do
  let (d, op) ← decodeFixedNat 4 d
  match op with
  | 0 => Prod.map id .Var                          <$> decodeVar nextDeBruijn d
  | 1 => Prod.map id .Delay                        <$> decodeTerm v nextDeBruijn d
  | 2 => Prod.map id (.Lam (varName nextDeBruijn)) <$> decodeTerm v (nextDeBruijn + 1) d
  | 3 => do
      let (d' , t₁) ← decodeTerm v nextDeBruijn d
      let (d'', t₂) ← decodeTerm v nextDeBruijn d'
      .some (d'', .Apply t₁ t₂)
  | 4 => Prod.map id .Const   <$> decodeConst d
  | 5 => Prod.map id .Force   <$> decodeTerm v nextDeBruijn d
  | 6 => .some (d, .Error)
  | 7 => Prod.map id .Builtin <$> decodeBuiltinFun v d
  | 8 => do
      let _        ← if v < .Version 1 1 0 then .none else .some ()
      let (d' , i) ← Option.filter (λ (_, i) => i < 2 ^ 64) (decodeNat d)
      let (d'', l) ← decodeList (decodeTerm v nextDeBruijn) d'
      .some (d'', .Constr i l)
  | 9 => do
      let _        ← if v < .Version 1 1 0 then .none else .some ()
      let (d' , u) ← decodeTerm v nextDeBruijn d
      let (d'', l) ← decodeList (decodeTerm v nextDeBruijn) d'
      .some (d'', .Case u l)
  | _ => .none

/- Decodes the Version of the Program. -/
def decodeVersion (d : DecodeState) : Option (DecodeState × Version) := do
  let (d'  , a) ← decodeNat d
  let (d'' , b) ← decodeNat d'
  let (d''', c) ← decodeNat d''
  .some (d''', .Version a b c)

/- Decodes a Program from a `DecodeState`. -/
def decodeProgramFromState (d : DecodeState) : Option Program := do
  let (d' , version) ← decodeVersion d
  let (d'',  t     ) ← decodeTerm version 0 d'
  let d'''           ← unpad d''
  let _              ← Option.filter (λ () => d'''.absBit = d'''.totalBits) (.some ())
  .some (.Program version t)

/- Decodes a single hex digit to its 4-bit value. -/
def hexDigitValue : Char → Option Nat
  | '0'       => .some  0
  | '1'       => .some  1
  | '2'       => .some  2
  | '3'       => .some  3
  | '4'       => .some  4
  | '5'       => .some  5
  | '6'       => .some  6
  | '7'       => .some  7
  | '8'       => .some  8
  | '9'       => .some  9
  | 'a' | 'A' => .some 10
  | 'b' | 'B' => .some 11
  | 'c' | 'C' => .some 12
  | 'd' | 'D' => .some 13
  | 'e' | 'E' => .some 14
  | 'f' | 'F' => .some 15
  | _         => .none

/- Converts a hex string to a `ByteArray`. Each pair of hex digits becomes one byte.
   Returns `.none` for odd-length inputs or non-hex characters. -/
def hexStringToByteArray (s : String) : Option ByteArray :=
  go s.data #[]
where
  go : List Char → Array UInt8 → Option ByteArray
  | h₁ :: h₂ :: t, acc => do
      let v₁ ← hexDigitValue h₁
      let v₂ ← hexDigitValue h₂
      go t (acc.push (16 * v₁ + v₂).toUInt8)
  | []           , acc => .some ⟨acc⟩
  | _            , _   => .none

/- Decodes a Program from a hex string. -/
def decodeProgramFromHexString (hexString : String) : Option Program :=
  hexStringToByteArray hexString >>= decodeProgramFromByteArray
where
  decodeProgramFromByteArray (b : ByteArray) : Option Program :=
    decodeProgramFromState { input := b, bytePos := 0, bitPos := 0 }

/- Decodes a Program from a `ByteArray`. -/
def decodeProgramFromByteArray (b : ByteArray) : Option Program :=
  decodeProgramFromState { input := b, bytePos := 0, bitPos := 0 }

end Internal

export Internal
  (
    decodeProgramFromHexString
    decodeProgramFromByteArray
  )

end PlutusCore.UPLC.FlatEncoding
