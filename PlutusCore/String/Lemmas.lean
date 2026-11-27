import PlutusCore.String.Basic

namespace PlutusCore.String
open PlutusCore.ByteString (ByteString)

/-! ## Theorems on PlutusCore String representation and builtin functions. -/

@[simp] theorem appendString_rfl (x y : String) : appendString x y = x ++ y := rfl

@[simp] theorem equalsString_rfl (x y : String) : equalsString x y = (x == y) := rfl

/-! ### UTF-8 encoding preserves the order of characters and strings

`utf8EncodeChar` is first characterised arithmetically (`utf8EncodeChar_toNat`); the order
facts are then proved on `Nat` byte lists, where `omega` can compare the byte fields. -/

/-- Byte values of the UTF-8 encoding of the code point `n < 0x110000`, as plain arithmetic.
    (The 4-byte lead byte needs no `% 8` since `n / 0x40000 ≤ 4`.) -/
def utf8EncodeNat (n : Nat) : List Nat :=
       if n ≤   0x7f then [n]
  else if n ≤  0x7ff then [0xc0 + n /   0x40 % 0x20, 0x80 + n % 0x40]
  else if n ≤ 0xffff then [0xe0 + n / 0x1000 % 0x10, 0x80 + n / 0x40 % 0x40, 0x80 + n % 0x40]
  else [0xf0 + n / 0x40000, 0x80 + n / 0x1000 % 0x40, 0x80 + n / 0x40 % 0x40, 0x80 + n % 0x40]

/-- Masking the low `k` bits of a byte and setting the high bits to `2 ^ k * a` is addition. -/
theorem UInt8.toNat_and_or (x m p : UInt8) (k a : Nat) (hm : m.toNat = 2 ^ k - 1) (hp : p.toNat = 2 ^ k * a) :
  (x &&& m ||| p).toNat = 2 ^ k * a + x.toNat % 2 ^ k :=
    by
      rw [UInt8.toNat_or, UInt8.toNat_and, hm, hp, Nat.and_two_pow_sub_one_eq_mod, Nat.or_comm,
          Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k))]

theorem Char.toNat_ofUInt8 (b : UInt8) : (Char.ofUInt8 b).toNat = b.toNat := by
  simp [Char.ofUInt8, Char.toNat]

theorem Char.toNat_lt_max (c : Char) : c.toNat < 0x110000 := by
  have := c.valid
  simp [UInt32.isValidChar, Nat.isValidChar] at this
  simp [Char.toNat]
  omega

theorem Char.toNat_lt_iff {a b : Char} : a.toNat < b.toNat ↔ a < b := by
  rw [Char.lt_iff_val_lt_val, UInt32.lt_iff_toNat_lt]; rfl

theorem Char.toNat_eq_iff {a b : Char} : a.toNat = b.toNat ↔ a = b :=
  ⟨fun h => Char.ext (UInt32.toNat_inj.mp h), fun h => h ▸ rfl⟩

/-- The bytes produced by `utf8EncodeChar` are those of `utf8EncodeNat`. -/
theorem utf8EncodeChar_toNat (c : Char) :
  (utf8EncodeChar c).map Char.toNat = utf8EncodeNat c.toNat :=
    by
      have h2 (x : UInt8) := UInt8.toNat_and_or x 0x1f 0xc0 5  6 rfl rfl
      have h3 (x : UInt8) := UInt8.toNat_and_or x 0x0f 0xe0 4 14 rfl rfl
      have h4 (x : UInt8) := UInt8.toNat_and_or x 0x07 0xf0 3 30 rfl rfl
      have hc (x : UInt8) := UInt8.toNat_and_or x 0x3f 0x80 6  2 rfl rfl
      simp only [Nat.reducePow, Nat.reduceMul] at h2 h3 h4 hc
      unfold utf8EncodeChar utf8EncodeNat
      simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat]
      have hv : c.val.toNat = c.toNat := rfl
      rw [hv]
      by_cases a1 : c.toNat ≤ 127
      · simp [a1]
      by_cases a2 : c.toNat ≤ 2047
      · simp only [a1, a2, if_false, if_true, List.map_cons, List.map_nil, Char.toNat_ofUInt8, h2, hc,
          UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hv,
          UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow, List.cons.injEq, and_true]
        omega
      by_cases a3 : c.toNat ≤ 65535
      · simp only [a1, a2, a3, if_false, if_true, List.map_cons, List.map_nil, Char.toNat_ofUInt8, h3,
          hc, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hv,
          UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow, List.cons.injEq, and_true]
        omega
      · have := Char.toNat_lt_max c
        simp only [a1, a2, a3, if_false, List.map_cons, List.map_nil, Char.toNat_ofUInt8, h4, hc,
          UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hv,
          UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow, List.cons.injEq, and_true]
        omega

theorem utf8EncodeChar_ne_nil (c : Char) : utf8EncodeChar c ≠ [] :=
  by
    intro h
    have := utf8EncodeChar_toNat c
    rw [h] at this
    unfold utf8EncodeNat at this
    repeat' split at this
    all_goals simp at this

/-- The lexicographic order on character lists is the one on their code points. -/
theorem map_toNat_lt_iff (l1 l2 : List Char) :
  l1.map Char.toNat < l2.map Char.toNat ↔ l1 < l2 :=
    by
      induction l1 generalizing l2 with
      | nil         => cases l2 <;> simp
      | cons a s ih =>
          cases l2 with
          | nil      => simp
          | cons b t => simp [List.cons_lt_cons_iff, ih, Char.toNat_lt_iff, Char.toNat_eq_iff]

theorem append_lt_append_left_iff {α} [LT α] [Std.Irrefl (· < · : α → α → Prop)] (p X Y : List α) :
  p ++ X < p ++ Y ↔ X < Y :=
    by
      induction p with
      | nil         => rfl
      | cons a p ih => simp [ih]

/-- Smaller code points have lexicographically smaller encodings, whatever follows them: the
    encodings already differ within their common length (UTF-8 is prefix-free). -/
theorem utf8EncodeNat_append_lt {n1 n2 : Nat} (h2 : n2 < 0x110000) (h : n1 < n2) (X Y : List Nat) :
  utf8EncodeNat n1 ++ X < utf8EncodeNat n2 ++ Y :=
    by
      unfold utf8EncodeNat
      repeat' split
      all_goals
        simp only [List.cons_append, List.nil_append, List.cons_lt_cons_iff]
        -- Walk down the bytes: a byte is either smaller, or (given `n1 < n2`) equal.
        repeat (first
          | exact Or.inl (by omega)
          | refine Classical.or_iff_not_imp_left.mpr fun _ => ⟨by omega, ?_⟩)

theorem utf8EncodeNat_lt_iff {n1 n2 : Nat} (h1 : n1 < 0x110000) (h2 : n2 < 0x110000) :
  utf8EncodeNat n1 < utf8EncodeNat n2 ↔ n1 < n2 :=
    by
      constructor
      · intro h
        rcases Nat.lt_trichotomy n1 n2 with h' | rfl | h'
        · exact h'
        · exact absurd h (List.lt_irrefl _)
        · have := utf8EncodeNat_append_lt h1 h' [] []
          simp only [List.append_nil] at this
          exact absurd h (List.lt_asymm this)
      · intro h
        simpa using utf8EncodeNat_append_lt h2 h [] []

theorem utf8EncodeChar_append_lt {c1 c2 : Char} (h : c1 < c2) (X Y : List Char) :
  utf8EncodeChar c1 ++ X < utf8EncodeChar c2 ++ Y :=
    by
      rw [← map_toNat_lt_iff, List.map_append, List.map_append, utf8EncodeChar_toNat,
          utf8EncodeChar_toNat]
      exact utf8EncodeNat_append_lt (Char.toNat_lt_max c2) (Char.toNat_lt_iff.mpr h) _ _

theorem utf8EncodeChar_lt_imp_lt (c1 c2 : Char) :
  utf8EncodeChar c1 < utf8EncodeChar c2 → c1 < c2 :=
    by
      intro h
      rw [← map_toNat_lt_iff, utf8EncodeChar_toNat, utf8EncodeChar_toNat,
          utf8EncodeNat_lt_iff (Char.toNat_lt_max c1) (Char.toNat_lt_max c2)] at h
      exact Char.toNat_lt_iff.mp h

theorem lt_imp_utf8EncodeChar_lt (c1 c2 : Char) :
  c1 < c2 → utf8EncodeChar c1 < utf8EncodeChar c2 :=
    by
      intro h
      simpa using utf8EncodeChar_append_lt h [] []

@[simp] theorem utff8EncodeChar_lt_iff_lt (c1 c2 : Char) :
  utf8EncodeChar c1 < utf8EncodeChar c2 ↔ c1 < c2 :=
    by
      apply Iff.intro
      . apply utf8EncodeChar_lt_imp_lt
      . apply lt_imp_utf8EncodeChar_lt

/-- Encoding a character list preserves its lexicographic order. -/
theorem flatMap_utf8EncodeChar_lt_iff (l1 l2 : List Char) :
  l1.flatMap utf8EncodeChar < l2.flatMap utf8EncodeChar ↔ l1 < l2 :=
    by
      induction l1 generalizing l2 with
      | nil =>
          cases l2 with
          | nil => simp
          | cons b t =>
            obtain ⟨x, r, hx⟩ := List.exists_cons_of_ne_nil (utf8EncodeChar_ne_nil b)
            simp [hx]
      | cons a s ih =>
          cases l2 with
          | nil => simp
          | cons b t =>
              simp only [List.flatMap_cons]
              by_cases hab : a < b
              · exact iff_of_true (utf8EncodeChar_append_lt hab _ _)
                  (List.cons_lt_cons_iff.mpr (Or.inl hab))
              by_cases hba : b < a
              · exact iff_of_false (List.lt_asymm (utf8EncodeChar_append_lt hba _ _))
                  (List.lt_asymm (List.cons_lt_cons_iff.mpr (Or.inl hba)))
              have : a = b := Char.le_antisymm (Char.not_lt.mp hba) (Char.not_lt.mp hab)
              subst this
              rw [append_lt_append_left_iff, List.cons_lt_cons_self, ih]

theorem toUTF8_lt_imp_lt (x y : String) : encodeUtf8 x < encodeUtf8 y → x < y :=
  (flatMap_utf8EncodeChar_lt_iff x.data y.data).mp

theorem lt_imp_toUTF8_lt (x y : String) : x < y → encodeUtf8 x < encodeUtf8 y :=
  (flatMap_utf8EncodeChar_lt_iff x.data y.data).mpr

@[simp] theorem toUTF8_lt_iff_lt (x y : String) :
  encodeUtf8 x < encodeUtf8 y ↔ x < y :=
    by
      apply Iff.intro
      . apply toUTF8_lt_imp_lt
      . apply lt_imp_toUTF8_lt

end  PlutusCore.String
