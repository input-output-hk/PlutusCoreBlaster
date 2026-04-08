import PlutusCore.UPLC.Term.Basic
import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2

namespace PlutusCore.UPLC.Term

open PlutusCore.Crypto.BLS12_381.G1 (bls12_381_G1_equal)
open PlutusCore.Crypto.BLS12_381.G2 (bls12_381_G2_equal)

-- BEq for Const (manual, partial due to recursive ConstList and Pair constructors)
private partial def constBeq : Const → Const → Bool
  | .Integer a             , .Integer b              => a == b
  | .ByteString a          , .ByteString b           => a == b
  | .String a              , .String b               => a == b
  | .Unit                  , .Unit                   => true
  | .Bool a                , .Bool b                 => a == b
  | .ConstList a           , .ConstList b            => a.length == b.length && (a.zip b).all (fun (x, y) => constBeq x y)
  | .ConstDataList a       , .ConstDataList b        => a == b
  | .ConstPairDataList a   , .ConstPairDataList b    => a == b
  | .Pair (a1, a2)         , .Pair (b1, b2)          => constBeq a1 b1 && constBeq a2 b2
  | .PairData a            , .PairData b             => a == b
  | .Data a                , .Data b                 => a == b
  | .Bls12_381_G1_element a, .Bls12_381_G1_element b => bls12_381_G1_equal a b
  | .Bls12_381_G2_element a, .Bls12_381_G2_element b => bls12_381_G2_equal a b
  | .Bls12_381_MlResult   a, .Bls12_381_MlResult   b => a == b
  | _                      , _                       => false

instance : BEq Const := ⟨constBeq⟩

instance : Repr AtomicType where
  reprPrec t _ :=
    match t with
    | .TypeInteger              => "Integer"
    | .TypeByteString           => "ByteString"
    | .TypeString               => "String"
    | .TypeBool                 => "Bool"
    | .TypeUnit                 => "Unit"
    | .TypeData                 => "Data"
    | .TypeBls12_381_G1_element => "TypeBls12_381_G1_element"
    | .TypeBls12_381_G2_element => "TypeBls12_381_G2_element"
    | .TypeBls12_381_MlResult   => "TypeBls12_381_MlResult"

instance {α β} [LT α] [LT β] : LT (Prod α β) where
  lt | (a₁, b₁), (a₂, b₂) => (a₁ < a₂) ∨ (a₁ = a₂ ∧ b₁ < b₂)

instance {α β} [LT α] [LT β] [DecidableLT α] [DecidableEq α] [dltb : DecidableLT β] : DecidableRel (LT.lt : Prod α β → Prod α β → Prop) :=
  λ (a₁, b₁) (a₂, b₂) =>
    if h : a₁ < a₂
      then isTrue (Or.inl h)
    else if heq : a₁ = a₂ then
      match dltb b₁ b₂ with
      | isTrue  hlt  => isTrue (Or.inr ⟨heq, hlt⟩)
      | isFalse hnlt => isFalse (fun h => by
          cases h
          · contradiction
          · have hl : a₁ = a₂ ∧ b₁ < b₂ := by assumption
            obtain ⟨_, _⟩ := hl
            contradiction
        )
    else isFalse (fun h => by
           cases h
           · contradiction
           · have hl : a₁ = a₂ ∧ b₁ < b₂ := by assumption
             obtain ⟨_, _⟩ := hl
             contradiction
         )

instance : LT Version where
  lt | .Version a₁ b₁ c₁, .Version a₂ b₂ c₂ => (a₁, b₁, c₁) < (a₂, b₂, c₂)

instance [dltp : DecidableLT (Nat × Nat × Nat)] : DecidableRel (LT.lt : Version → Version → Prop) :=
  λ (.Version a₁ b₁ c₁) (.Version a₂ b₂ c₂) => dltp (a₁, b₁, c₁) (a₂, b₂, c₂)

instance : Inhabited Program where
  default := .Program (.Version 0 0 0) .Error

end PlutusCore.UPLC.Term
