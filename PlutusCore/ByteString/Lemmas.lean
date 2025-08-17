import PlutusCore.ByteString.Basic

namespace PlutusCore.ByteString
open PlutusCore.Integer

/-! ## Theorem on ByteString representation and builtin functions. -/

@[simp] theorem appendByteString_rfl (x y : ByteString) : appendByteString x y = x.data ++ y.data := rfl

-- TODO: complete the following proofs
theorem stringToByteString_lt_imp_lt (s1 s2 : String) :
  ByteString.stringToByteString s1 < ByteString.stringToByteString s2 → s1 < s2 := by
    intro h;
    unfold LT.lt at h;
    simp [PlutusCore.ByteStringInternal.LTByteString, ByteString.stringToByteString] at h
    assumption

theorem lt_imp_stringToByteString_lt (s1 s2 : String) :
  s1 < s2 → ByteString.stringToByteString s1 < ByteString.stringToByteString s2 := by
    intro h;
    unfold LT.lt;
    simp [PlutusCore.ByteStringInternal.LTByteString, ByteString.stringToByteString]
    assumption

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

@[simp] theorem lengthOfByteString_rfl (bs : ByteString) : lengthOfByteString bs = Int.ofNat bs.length := rfl

@[simp] theorem size_cons (u : UInt8) (bs : ByteString) : (ByteString.cons u bs).length = 1 + bs.length := by simp [ByteString.cons]


end PlutusCore.ByteString
