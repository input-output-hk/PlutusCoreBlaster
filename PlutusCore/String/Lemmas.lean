import PlutusCore.String.Basic

namespace PlutusCore.String
open PlutusCore.ByteString (ByteString)

/-! ## Theorems on PlutusCore String representation and builtin functions. -/

@[simp] theorem appendString_rfl (x y : String) : appendString x y = x ++ y := rfl

@[simp] theorem equalsString_rfl (x y : String) : equalsString x y = (x == y) := rfl

@[simp] theorem encodeUft8_rfl (x : String) : encodeUtf8 x = x.toUTF8 := rfl

@[simp] theorem decodeUtf8_rfl (bs : ByteString) :
  decodeUtf8 bs =
    if h : String.validateUTF8 bs
    then pure (String.fromUTF8 bs h)
    else throw "decodeUtf8: invalid ByteString"
  := rfl

-- TODO : complete the following proofs
theorem utf8EncodeChar_lt_imp_lt (c1 c2 : Char) :
    String.utf8EncodeChar c1 < String.utf8EncodeChar c2 → c1 < c2 := by sorry

theorem lt_imp_utf8EncodeChar_lt (c1 c2 : Char) :
    c1 < c2 → String.utf8EncodeChar c1 < String.utf8EncodeChar c2 := by sorry

@[simp] theorem utff8EncodeChar_lt_iff_lt (c1 c2 : Char) :
   String.utf8EncodeChar c1 < String.utf8EncodeChar c2 ↔ c1 < c2 := by
   apply Iff.intro
   . apply utf8EncodeChar_lt_imp_lt
   . apply lt_imp_utf8EncodeChar_lt

theorem toUTF8_lt_imp_lt (x y : String) : x.toUTF8 < y.toUTF8 → x < y := by sorry
theorem lt_imp_toUTF8_lt (x y : String) : x < y → x.toUTF8 < y.toUTF8 := by sorry

@[simp] theorem toUTF8_lt_iff_lt (x y : String) : x.toUTF8 < y.toUTF8 ↔ x < y := by
  apply Iff.intro
  . apply toUTF8_lt_imp_lt
  . apply lt_imp_toUTF8_lt

theorem encodeUft8_lt_imp_lt (x y : String) : encodeUtf8 x < encodeUtf8 y → x < y := by sorry

theorem lt_imp_encodeUft8_lt (x y : String) : x < y → encodeUtf8 x < encodeUtf8 y := by sorry

@[simp] theorem encodeUft8_lt_iff_lt (x y : String) : encodeUtf8 x < encodeUtf8 y ↔ x < y := by
  apply Iff.intro
  . apply encodeUft8_lt_imp_lt
  . apply lt_imp_encodeUft8_lt


end  PlutusCore.String
