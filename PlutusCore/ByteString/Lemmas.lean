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
  then pure { data := PlutusCore.Bytes.byteStr n.toNat ++ bs.data }
  else throw "consByteStringV2: invalid byte representation" := by rfl

@[simp] theorem lengthOfByteString_rfl (bs : ByteString) : lengthOfByteString bs = Int.ofNat bs.length := rfl

@[simp] theorem size_cons (u : UInt8) (bs : ByteString) : (ByteString.cons u bs).length = 1 + bs.length := by simp [ByteString.cons]

/-! ## The byte-level builtins compute what they computed through `Char`

`consByteString*`, `sliceByteString` and `indexByteString` go through `PlutusCore.Bytes` so that
Blaster can translate them. The theorems below show they still compute the `Char`-based formulas
they replaced, on every string. -/

section CharFormulas
open PlutusCore.Bytes

set_option maxRecDepth 100000 in
theorem byteStr_eq_ofUInt8 : ∀ b, b < 256 → byteStr b = String.singleton (Char.ofUInt8 b.toUInt8) := by
  decide

theorem consByteStringV1_eq_cons (n : Integer) (bs : ByteString) :
    consByteStringV1 n bs =
    match (modInteger n 256) with
    | Except.ok m => ByteString.cons m.toNat.toUInt8 bs
    | Except.error _ => unreachable! := by
  have hfmod : Int.fmod n 256 = n % 256 := Int.fmod_eq_emod_of_nonneg n (by decide)
  have hlt : (n % 256).toNat < 256 := by omega
  simp only [consByteStringV1, modInteger, ByteString.cons]
  rw [byteStr_eq_ofUInt8 _ hlt, ← hfmod]
  rfl

theorem consByteStringV2_eq_cons (n : Integer) (bs : ByteString) :
    consByteStringV2 n bs =
    if 0 <= n && n <= 255
    then pure (ByteString.cons n.toNat.toUInt8 bs)
    else throw "consByteStringV2: invalid byte representation" := by
  rw [consByteStringV2_rfl]
  split
  · next h =>
    have hlt : n.toNat < 256 := by revert h; simp only [Integer, Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [ByteString.cons]
    rw [byteStr_eq_ofUInt8 _ hlt]
  · rfl

theorem sliceByteString_eq_drop_take (s k : Integer) (bs : ByteString) :
    sliceByteString s k bs =
    { data := String.mk ((bs.data.toList.drop (Max.max s 0).toNat).take (Max.max k 0).toNat) } := by
  simp only [sliceByteString, takeB_eq, dropB_eq]
  rfl

theorem indexByteString_eq_getElem? (bs : ByteString) (j : Integer) :
    indexByteString bs j =
    if j < 0 then throw "indexByteString: index out of bounds"
    else
      match bs.data.toList[j.toNat]? with
      | none => throw "indexByteString: index out of bounds"
      | some c => pure c.toNat := by
  simp only [indexByteString, dropB_eq]
  split
  · rfl
  · rw [uncons_eq, ← List.head?_drop]
    simp only [String.toList]
    cases bs.data.data.drop j.toNat <;> rfl

end CharFormulas


end PlutusCore.ByteString
