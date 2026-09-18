import PlutusCore.UPLC.Term.Basic
import PlutusCore.UPLC.Term.Instances

namespace PlutusCore.UPLC.Term

/-! ## Decidable equality for `Const` and `Term`

`deriving DecidableEq` fails on both types because each nests a `List` of itself, and a
derived `BEq` does not reduce under `decide`, so the comparisons are hand-written. No `BEq`
is declared here, since a second one would change `==` for every caller. -/

-- Used by `eqTerm`.
deriving instance DecidableEq for BuiltinFun

/-! ### `Const` -/

mutual
  def eqConst : Const → Const → Bool
    | .Integer a, .Integer b => a == b
    | .ByteString a, .ByteString b => a == b
    | .String a, .String b => a == b
    | .Unit, .Unit => true
    | .Bool a, .Bool b => a == b
    | .ConstList a, .ConstList b => eqConstList a b
    | .ConstDataList a, .ConstDataList b => a == b
    | .ConstPairDataList a, .ConstPairDataList b => a == b
    | .Pair (a1, a2), .Pair (b1, b2) => eqConst a1 b1 && eqConst a2 b2
    | .PairData a, .PairData b => a == b
    | .Data a, .Data b => a == b
    | .Bls12_381_G1_element a, .Bls12_381_G1_element b => a == b
    | .Bls12_381_G2_element a, .Bls12_381_G2_element b => a == b
    | .Bls12_381_MlResult a, .Bls12_381_MlResult b => a == b
    | _, _ => false

  def eqConstList : List Const → List Const → Bool
    | [], [] => true
    | a :: as, b :: bs => eqConst a b && eqConstList as bs
    | _, _ => false
end

mutual
  theorem eqConst_true_imp_eq : ∀ a b : Const, eqConst a b = true → a = b
    | .ConstList a, .ConstList b, h => by
        simp only [eqConst] at h
        rw [eqConstList_true_imp_eq a b h]
    | .Pair (a1, a2), .Pair (b1, b2), h => by
        simp only [eqConst, Bool.and_eq_true] at h
        rw [eqConst_true_imp_eq a1 b1 h.1, eqConst_true_imp_eq a2 b2 h.2]
    | .Integer _, b, h
    | .ByteString _, b, h
    | .String _, b, h
    | .Unit, b, h
    | .Bool _, b, h
    | .ConstDataList _, b, h
    | .ConstPairDataList _, b, h
    | .PairData _, b, h
    | .Data _, b, h
    | .Bls12_381_G1_element _, b, h
    | .Bls12_381_G2_element _, b, h
    | .Bls12_381_MlResult _, b, h => by cases b <;> simp_all [eqConst]
    | .ConstList _, .Integer _, h | .ConstList _, .ByteString _, h | .ConstList _, .String _, h
    | .ConstList _, .Unit, h | .ConstList _, .Bool _, h | .ConstList _, .ConstDataList _, h
    | .ConstList _, .ConstPairDataList _, h | .ConstList _, .Pair _, h
    | .ConstList _, .PairData _, h | .ConstList _, .Data _, h
    | .ConstList _, .Bls12_381_G1_element _, h | .ConstList _, .Bls12_381_G2_element _, h
    | .ConstList _, .Bls12_381_MlResult _, h
    | .Pair _, .Integer _, h | .Pair _, .ByteString _, h | .Pair _, .String _, h
    | .Pair _, .Unit, h | .Pair _, .Bool _, h | .Pair _, .ConstList _, h
    | .Pair _, .ConstDataList _, h | .Pair _, .ConstPairDataList _, h
    | .Pair _, .PairData _, h | .Pair _, .Data _, h
    | .Pair _, .Bls12_381_G1_element _, h | .Pair _, .Bls12_381_G2_element _, h
    | .Pair _, .Bls12_381_MlResult _, h => by simp [eqConst] at h

  theorem eqConstList_true_imp_eq : ∀ a b : List Const, eqConstList a b = true → a = b
    | [], [], _ => rfl
    | a :: as, b :: bs, h => by
        simp only [eqConstList, Bool.and_eq_true] at h
        rw [eqConst_true_imp_eq a b h.1, eqConstList_true_imp_eq as bs h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [eqConstList] at h
end

mutual
  theorem eqConst_reflexive : ∀ a : Const, eqConst a a = true
    | .Integer _ | .ByteString _ | .String _ | .Unit | .Bool _
    | .ConstDataList _ | .ConstPairDataList _ | .PairData _ | .Data _
    | .Bls12_381_G1_element _ | .Bls12_381_G2_element _
    | .Bls12_381_MlResult _ => by simp [eqConst]
    | .ConstList a => by simp only [eqConst]; exact eqConstList_reflexive a
    | .Pair (a1, a2) => by
        simp only [eqConst, Bool.and_eq_true]
        exact ⟨eqConst_reflexive a1, eqConst_reflexive a2⟩

  theorem eqConstList_reflexive : ∀ a : List Const, eqConstList a a = true
    | [] => by simp [eqConstList]
    | a :: as => by
        simp only [eqConstList, Bool.and_eq_true]
        exact ⟨eqConst_reflexive a, eqConstList_reflexive as⟩
end

theorem eqConst_false_imp_not_eq (a b : Const) : eqConst a b = false → a ≠ b :=
  fun h => eq_false_imp_ne eqConst_reflexive h

def Const.decEq (a b : Const) : Decidable (Eq a b) :=
  match h : eqConst a b with
  | true => isTrue (eqConst_true_imp_eq _ _ h)
  | false => isFalse (eqConst_false_imp_not_eq _ _ h)

instance : DecidableEq Const := Const.decEq

/-! ### `Term` -/

mutual
  def eqTerm : Term → Term → Bool
    | .Var i, .Var j => i == j
    | .Const a, .Const b => eqConst a b
    | .Builtin a, .Builtin b => decide (a = b)
    | .Lam x a, .Lam y b => x == y && eqTerm a b
    | .Apply f a, .Apply g b => eqTerm f g && eqTerm a b
    | .Delay a, .Delay b => eqTerm a b
    | .Force a, .Force b => eqTerm a b
    | .Constr i a, .Constr j b => i == j && eqTermList a b
    | .Case a as, .Case b bs => eqTerm a b && eqTermList as bs
    | .Error, .Error => true
    | _, _ => false

  def eqTermList : List Term → List Term → Bool
    | [], [] => true
    | a :: as, b :: bs => eqTerm a b && eqTermList as bs
    | _, _ => false
end

mutual
  theorem eqTerm_true_imp_eq : ∀ a b : Term, eqTerm a b = true → a = b
    | .Const a, .Const b, h => by
        simp only [eqTerm] at h
        rw [eqConst_true_imp_eq a b h]
    | .Lam x a, .Lam y b, h => by
        simp only [eqTerm, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, eqTerm_true_imp_eq a b h.2]
    | .Apply f a, .Apply g b, h => by
        simp only [eqTerm, Bool.and_eq_true] at h
        rw [eqTerm_true_imp_eq f g h.1, eqTerm_true_imp_eq a b h.2]
    | .Delay a, .Delay b, h => by
        simp only [eqTerm] at h
        rw [eqTerm_true_imp_eq a b h]
    | .Force a, .Force b, h => by
        simp only [eqTerm] at h
        rw [eqTerm_true_imp_eq a b h]
    | .Constr i a, .Constr j b, h => by
        simp only [eqTerm, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, eqTermList_true_imp_eq a b h.2]
    | .Case a as, .Case b bs, h => by
        simp only [eqTerm, Bool.and_eq_true] at h
        rw [eqTerm_true_imp_eq a b h.1, eqTermList_true_imp_eq as bs h.2]
    | .Var _, b, h | .Builtin _, b, h | .Error, b, h => by cases b <;> simp_all [eqTerm]
    | .Const _, .Var _, h | .Const _, .Builtin _, h | .Const _, .Lam _ _, h
    | .Const _, .Apply _ _, h | .Const _, .Delay _, h | .Const _, .Force _, h
    | .Const _, .Constr _ _, h | .Const _, .Case _ _, h | .Const _, .Error, h
    | .Lam _ _, .Var _, h | .Lam _ _, .Const _, h | .Lam _ _, .Builtin _, h
    | .Lam _ _, .Apply _ _, h | .Lam _ _, .Delay _, h | .Lam _ _, .Force _, h
    | .Lam _ _, .Constr _ _, h | .Lam _ _, .Case _ _, h | .Lam _ _, .Error, h
    | .Apply _ _, .Var _, h | .Apply _ _, .Const _, h | .Apply _ _, .Builtin _, h
    | .Apply _ _, .Lam _ _, h | .Apply _ _, .Delay _, h | .Apply _ _, .Force _, h
    | .Apply _ _, .Constr _ _, h | .Apply _ _, .Case _ _, h | .Apply _ _, .Error, h
    | .Delay _, .Var _, h | .Delay _, .Const _, h | .Delay _, .Builtin _, h
    | .Delay _, .Lam _ _, h | .Delay _, .Apply _ _, h | .Delay _, .Force _, h
    | .Delay _, .Constr _ _, h | .Delay _, .Case _ _, h | .Delay _, .Error, h
    | .Force _, .Var _, h | .Force _, .Const _, h | .Force _, .Builtin _, h
    | .Force _, .Lam _ _, h | .Force _, .Apply _ _, h | .Force _, .Delay _, h
    | .Force _, .Constr _ _, h | .Force _, .Case _ _, h | .Force _, .Error, h
    | .Constr _ _, .Var _, h | .Constr _ _, .Const _, h | .Constr _ _, .Builtin _, h
    | .Constr _ _, .Lam _ _, h | .Constr _ _, .Apply _ _, h | .Constr _ _, .Delay _, h
    | .Constr _ _, .Force _, h | .Constr _ _, .Case _ _, h | .Constr _ _, .Error, h
    | .Case _ _, .Var _, h | .Case _ _, .Const _, h | .Case _ _, .Builtin _, h
    | .Case _ _, .Lam _ _, h | .Case _ _, .Apply _ _, h | .Case _ _, .Delay _, h
    | .Case _ _, .Force _, h | .Case _ _, .Constr _ _, h
    | .Case _ _, .Error, h => by simp [eqTerm] at h

  theorem eqTermList_true_imp_eq : ∀ a b : List Term, eqTermList a b = true → a = b
    | [], [], _ => rfl
    | a :: as, b :: bs, h => by
        simp only [eqTermList, Bool.and_eq_true] at h
        rw [eqTerm_true_imp_eq a b h.1, eqTermList_true_imp_eq as bs h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [eqTermList] at h
end

mutual
  theorem eqTerm_reflexive : ∀ a : Term, eqTerm a a = true
    | .Var _ | .Builtin _ | .Error => by simp [eqTerm]
    | .Const a => by simp only [eqTerm]; exact eqConst_reflexive a
    | .Lam _ a => by
        simp only [eqTerm, Bool.and_eq_true, beq_self_eq_true, true_and]
        exact eqTerm_reflexive a
    | .Apply f a => by
        simp only [eqTerm, Bool.and_eq_true]
        exact ⟨eqTerm_reflexive f, eqTerm_reflexive a⟩
    | .Delay a => by simp only [eqTerm]; exact eqTerm_reflexive a
    | .Force a => by simp only [eqTerm]; exact eqTerm_reflexive a
    | .Constr _ a => by
        simp only [eqTerm, Bool.and_eq_true, beq_self_eq_true, true_and]
        exact eqTermList_reflexive a
    | .Case a as => by
        simp only [eqTerm, Bool.and_eq_true]
        exact ⟨eqTerm_reflexive a, eqTermList_reflexive as⟩

  theorem eqTermList_reflexive : ∀ a : List Term, eqTermList a a = true
    | [] => by simp [eqTermList]
    | a :: as => by
        simp only [eqTermList, Bool.and_eq_true]
        exact ⟨eqTerm_reflexive a, eqTermList_reflexive as⟩
end

theorem eqTerm_false_imp_not_eq (a b : Term) : eqTerm a b = false → a ≠ b :=
  fun h => eq_false_imp_ne eqTerm_reflexive h

def Term.decEq (a b : Term) : Decidable (Eq a b) :=
  match h : eqTerm a b with
  | true => isTrue (eqTerm_true_imp_eq _ _ h)
  | false => isFalse (eqTerm_false_imp_not_eq _ _ h)

instance : DecidableEq Term := Term.decEq

/-! ### `Version` and `Program` -/

deriving instance DecidableEq for Version
deriving instance DecidableEq for Program

example : DecidableEq Version := inferInstance
example : DecidableEq Program := inferInstance

/-! ### The two equalities on `Term` -/

example : (Term.Lam "x" Term.Error == Term.Lam "y" Term.Error) = true := rfl

example : Term.Lam "x" Term.Error ≠ Term.Lam "y" Term.Error := by decide

example : Term.Lam "x" Term.Error = Term.Lam "x" Term.Error := by decide

-- These catch a second `BEq Const` or `BEq Term` taking precedence over the hand-written ones.
example : (inferInstance : BEq Const) = instBEqConst := rfl

example : (inferInstance : BEq Term) = instBEqTerm := rfl

/-- `==` on `Term` skips the binder name, so it cannot be lawful. -/
theorem instBEqTerm_not_lawful : ¬ (∀ a b : Term, (a == b) = true → a = b) := by
  intro h
  have := h (Term.Lam "x" Term.Error) (Term.Lam "y" Term.Error) rfl
  simp at this

/-! ### A BLS12-381 constant, decided

`==` sends these through the `opaque` `bls12_381_G1_equal`, which does not reduce.
`Const.decEq` compares the underlying `Point`, which does. -/

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    = Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1 := by decide

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    ≠ Const.Bls12_381_G1_element .infinity := by decide

/-! ### `LawfulBEq Const` does not synthesize -/

/-- error: failed to synthesize
  LawfulBEq Const

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth LawfulBEq Const

end PlutusCore.UPLC.Term
