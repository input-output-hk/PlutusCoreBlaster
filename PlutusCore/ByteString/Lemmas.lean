import PlutusCore.ByteString.Basic

namespace PlutusCore.ByteString
open PlutusCore.Integer

/-! ## Theorem on ByteString representation and builtin functions. -/

@[simp] theorem ByteString.beq_iff_eq (x y : ByteString) : x == y ↔ x = y := by
  apply Iff.intro
  . apply BEqByteString_true_imp_eq
  . intro h
    rw [h]
    apply LawfulBEqByteString.rfl

/-- NOTE: To be removed once migrated to latest Lean version -/
theorem ListUInt8_lt_irrefl (xs : List UInt8) : ¬ xs < xs := by
  simp [LT.lt]
  match xs with
  | [] => unfold Not
          intro h
          contradiction
  | hd :: tl =>
       unfold Not
       intro h1
       cases h1; rename_i h2
       . simp [LT.lt] at h2
         unfold UInt8.lt at h2
         have h3 : ¬ hd.val < hd.val := Nat.lt_irrefl hd.val
         contradiction
       . have h3 : ¬ List.lt tl tl := by apply ListUInt8_lt_irrefl tl
         contradiction

@[simp] theorem ByteString.lt_irrefl (x : ByteString) : ¬ x < x := by
  match x with
  | ByteArray.mk v =>
       unfold LT.lt LTByteString
       simp only [BEq.beq, LT.lt]
       apply ListUInt8_lt_irrefl

@[simp] theorem appendByteString_rfl (x y : ByteString) : appendByteString x y = x ++ y := rfl

-- TODO: complete the following proofs
theorem stringToByteString_lt_imp_lt (s1 s2 : String) :
  ByteString.stringToByteString s1 < ByteString.stringToByteString s2 → s1 < s2 := by sorry

theorem lt_imp_stringToByteString_lt (s1 s2 : String) :
  s1 < s2 → ByteString.stringToByteString s1 < ByteString.stringToByteString s2 := by sorry

@[simp] theorem stringToByteString_lt_iff_lt (s1 s2 : String) :
  ByteString.stringToByteString s1 < ByteString.stringToByteString s2 ↔ s1 < s2 := by
  apply Iff.intro
  . apply stringToByteString_lt_imp_lt
  . apply lt_imp_stringToByteString_lt

@[simp] theorem consByteStringV2_rfl (n : Integer) (bs : ByteString) :
  consByteStringV2 n bs =
  if 0 <= n && n <= 255
  then pure (ByteString.cons n.toNat.toUInt8 bs)
  else throw "consByteStringV2: invalid byte representation" := by rfl

@[simp] theorem lengthOfByteString_rfl (bs : ByteString) : lengthOfByteString bs = Int.ofNat bs.size := rfl

@[simp] theorem size_cons (u : UInt8) (bs : ByteString) : (ByteString.cons u bs).size = 1 + bs.size := by
  simp [ByteString.cons, ByteArray.size, Array.size]
  apply Nat.add_comm

end PlutusCore.ByteString
