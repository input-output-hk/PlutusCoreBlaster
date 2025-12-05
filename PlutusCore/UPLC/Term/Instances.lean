import PlutusCore.UPLC.Term.Basic

namespace PlutusCore.UPLC.Term

instance : Repr AtomicType where
  reprPrec t _ :=
    match t with
    | AtomicType.TypeInteger => "Integer"
    | AtomicType.TypeByteString => "ByteString"
    | AtomicType.TypeString => "String"
    | AtomicType.TypeBool => "Bool"
    | AtomicType.TypeUnit => "Unit"
    | AtomicType.TypeData => "Data"

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
