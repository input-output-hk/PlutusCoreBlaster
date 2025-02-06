import PlutusCore.ByteString.Basic

namespace PlutusCore.ByteString
open PlutusCore.Integer

/-! ## Theorem on ByteString representation and builtin functions. -/

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
