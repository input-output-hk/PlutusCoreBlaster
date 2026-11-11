import PlutusCore.UPLC.Term.Basic
import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2

namespace PlutusCore.UPLC.Term

mutual
  private def listBeq : List Const → List Const → Bool
    | h1 :: t1, h2 :: t2 =>
        if constBeq h1 h2
          then listBeq t1 t2
          else false
    | []      , []       => true
    | _       , _        => false

  private def constBeq : Const → Const → Bool
    | .Integer a             , .Integer b              => a == b
    | .ByteString a          , .ByteString b           => a == b
    | .String a              , .String b               => a == b
    | .Unit                  , .Unit                   => true
    | .Bool a                , .Bool b                 => a == b
    | .ConstList a           , .ConstList b            => listBeq a b
    | .ConstDataList a       , .ConstDataList b        => a == b
    | .ConstPairDataList a   , .ConstPairDataList b    => a == b
    | .Pair (a1, a2)         , .Pair (b1, b2)          => constBeq a1 b1 && constBeq a2 b2
    | .PairData a            , .PairData b             => a == b
    | .Data a                , .Data b                 => a == b
    | .Bls12_381_G1_element a, .Bls12_381_G1_element b => decide (a = b)
    | .Bls12_381_G2_element a, .Bls12_381_G2_element b => decide (a = b)
    | .Bls12_381_MlResult   a, .Bls12_381_MlResult   b => a == b
    | _                      , _                       => false
end

instance : BEq Const := ⟨constBeq⟩

mutual
  private def termListBeq : List Term → List Term → Bool
    | h1 :: t1, h2 :: t2 => termBeq h1 h2 && termListBeq t1 t2
    | []      , []       => true
    | _       , _        => false

  -- With de Bruijn indices this structural equality coincides with alpha-equivalence.
  private def termBeq : Term → Term → Bool
    | .Var i        , .Var j         => i == j
    | .Const c1     , .Const c2      => c1 == c2
    | .Builtin b1   , .Builtin b2    => b1 == b2
    | .Lam b1       , .Lam b2        => termBeq b1 b2
    | .Apply f1 a1  , .Apply f2 a2   => termBeq f1 f2 && termBeq a1 a2
    | .Delay t1     , .Delay t2      => termBeq t1 t2
    | .Force t1     , .Force t2      => termBeq t1 t2
    | .Constr n1 ts1, .Constr n2 ts2 => n1 == n2 && termListBeq ts1 ts2
    | .Case s1 hs1  , .Case s2 hs2   => termBeq s1 s2 && termListBeq hs1 hs2
    | .Error        , .Error         => true
    | _             , _              => false
end

instance : BEq Term := ⟨termBeq⟩

mutual
  theorem constBeq_true_imp_eq : ∀ a b : Const, constBeq a b = true → a = b := by
    intro a b h
    cases a <;> cases b <;> simp_all [constBeq]
    case ConstList.ConstList => exact listBeq_true_imp_eq _ _ h
    case Pair.Pair => exact Prod.ext (constBeq_true_imp_eq _ _ h.1) (constBeq_true_imp_eq _ _ h.2)

  theorem listBeq_true_imp_eq : ∀ a b : List Const, listBeq a b = true → a = b := by
    intro a b h
    cases a <;> cases b <;> simp_all [listBeq]
    case cons.cons => exact ⟨constBeq_true_imp_eq _ _ h.1, listBeq_true_imp_eq _ _ h.2⟩
end

mutual
  theorem constBeq_refl : ∀ a : Const, constBeq a a = true := by
    intro a
    cases a <;> simp [constBeq]
    case ConstList => exact listBeq_refl _
    case Pair => exact ⟨constBeq_refl _, constBeq_refl _⟩

  theorem listBeq_refl : ∀ a : List Const, listBeq a a = true := by
    intro a
    cases a <;> simp [listBeq]
    case cons => exact ⟨constBeq_refl _, listBeq_refl _⟩
end

instance : LawfulBEq Const where
  eq_of_beq {a b} := constBeq_true_imp_eq a b
  rfl {a} := constBeq_refl a

instance : DecidableEq Const := instDecidableEqOfLawfulBEq

mutual
  theorem termBeq_true_imp_eq : ∀ a b : Term, termBeq a b = true → a = b := by
    intro a b h
    cases a <;> cases b <;> simp_all [termBeq]
    case Lam.Lam | Delay.Delay | Force.Force => exact termBeq_true_imp_eq _ _ h
    case Apply.Apply => exact ⟨termBeq_true_imp_eq _ _ h.1, termBeq_true_imp_eq _ _ h.2⟩
    case Constr.Constr => exact termListBeq_true_imp_eq _ _ h.2
    case Case.Case => exact ⟨termBeq_true_imp_eq _ _ h.1, termListBeq_true_imp_eq _ _ h.2⟩

  theorem termListBeq_true_imp_eq : ∀ a b : List Term, termListBeq a b = true → a = b := by
    intro a b h
    cases a <;> cases b <;> simp_all [termListBeq]
    case cons.cons => exact ⟨termBeq_true_imp_eq _ _ h.1, termListBeq_true_imp_eq _ _ h.2⟩
end

mutual
  theorem termBeq_refl : ∀ a : Term, termBeq a a = true := by
    intro a
    cases a <;> simp [termBeq]
    case Lam | Delay | Force => exact termBeq_refl _
    case Apply => exact ⟨termBeq_refl _, termBeq_refl _⟩
    case Constr => exact termListBeq_refl _
    case Case => exact ⟨termBeq_refl _, termListBeq_refl _⟩

  theorem termListBeq_refl : ∀ a : List Term, termListBeq a a = true := by
    intro a
    cases a <;> simp [termListBeq]
    case cons => exact ⟨termBeq_refl _, termListBeq_refl _⟩
end

instance : LawfulBEq Term where
  eq_of_beq {a b} := termBeq_true_imp_eq a b
  rfl {a} := termBeq_refl a

instance : DecidableEq Term := instDecidableEqOfLawfulBEq

deriving instance DecidableEq for Version
deriving instance DecidableEq for Program

instance : Repr AtomicType where
  reprPrec t _ :=
    match t with
    | .TypeInteger              => "Integer"
    | .TypeByteString           => "ByteString"
    | .TypeString               => "String"
    | .TypeBool                 => "Bool"
    | .TypeUnit                 => "Unit"
    | .TypeData                 => "Data"
    | .TypeBls12_381_G1_element => "Bls12_381_G1_element"
    | .TypeBls12_381_G2_element => "Bls12_381_G2_element"
    | .TypeBls12_381_MlResult   => "Bls12_381_MlResult"

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
