import PlutusCore.String.Basic

namespace PlutusCore.String
open PlutusCore.ByteString (ByteString)

/-! ## Theorems on PlutusCore String representation and builtin functions. -/

@[simp] theorem appendString_rfl (x y : String) : appendString x y = x ++ y := rfl

@[simp] theorem equalsString_rfl (x y : String) : equalsString x y = (x == y) := rfl

-- -- TODO : complete the following proofs
theorem utf8EncodeChar_lt_imp_lt (c1 c2 : Char) : utf8EncodeChar c1 < utf8EncodeChar c2 → c1 < c2 := by sorry

theorem lt_imp_utf8EncodeChar_lt (c1 c2 : Char) :
    c1 < c2 → utf8EncodeChar c1 < utf8EncodeChar c2 := by sorry

@[simp] theorem utff8EncodeChar_lt_iff_lt (c1 c2 : Char) :
   utf8EncodeChar c1 < utf8EncodeChar c2 ↔ c1 < c2 := by
   apply Iff.intro
   . apply utf8EncodeChar_lt_imp_lt
   . apply lt_imp_utf8EncodeChar_lt

theorem toUTF8_lt_imp_lt (x y : String) : encodeUtf8 x < encodeUtf8 y → x < y := by sorry

theorem lt_imp_toUTF8_lt (x y : String) : x < y → encodeUtf8 x < encodeUtf8 y := by sorry

@[simp] theorem toUTF8_lt_iff_lt (x y : String) : encodeUtf8 x < encodeUtf8 y ↔ x < y := by
  apply Iff.intro
  . apply toUTF8_lt_imp_lt
  . apply lt_imp_toUTF8_lt



end  PlutusCore.String
