import PlutusCore.Bitwise.Basic

open PlutusCore.Integer
open PlutusCore.Bitwise.BitwiseInternal

namespace PlutusCore.Bitwise

/-! ## Theorems on Logical and Bitwise builtin functions. -/

def Except.isError (e : Except ε α) : Bool := not (Except.isOk e)

example : integerToByteString false 5 0x123456 = .ok "\x56\x34\x12\x00\x00" := rfl
example : integerToByteString false 4 0x123456 = .ok "\x56\x34\x12\x00"     := rfl
example : integerToByteString false 3 0x123456 = .ok "\x56\x34\x12"         := rfl
example : integerToByteString false 2 0x123456 |> Except.isError            := rfl
example : integerToByteString false 0 0x00     = .ok ""                     := by simp [integerLog2] ; rfl

example : integerToByteString true  5 0x123456 = .ok "\x00\x00\x12\x34\x56" := rfl
example : integerToByteString true  4 0x123456 = .ok     "\x00\x12\x34\x56" := rfl
example : integerToByteString true  3 0x123456 = .ok         "\x12\x34\x56" := rfl
example : integerToByteString true  2 0x123456 |> Except.isError            := rfl
example : integerToByteString true  0 0x00     = .ok ""                     := by simp [integerLog2]; rfl

-- itobs_be_loop (w, n) = ×, if 256 ^ w ≤ n
/-- Given `w` and `n`, if 256 ^ w ≤ n, `itobs_be_loop` returns an error -/
theorem itobs_be_loop_high_n (w n : Nat) (a : List Char) (hwn : 256 ^ w ≤ n) :
  itobs_be_loop w a n = .error "integerToByteString: cannot represent Integer in given number of bytes" := by
    induction w generalizing a n
    next =>
      unfold itobs_be_loop
      split <;> try contradiction
      rfl
    next p ih =>
      simp [itobs_be_loop]
      rw [ih]
      omega

/-- `repr256_le a` returns `n`, if `a` is the little-endian representation of `n`. -/
def repr256_le (a : List Char) : Nat :=
   a |> List.mapIdx (λ i c => (Char.toNat c) * 256 ^ i) |> List.sum

example : repr256_le (String.toList "\x56\x34\x12\x00\x00") = 0x123456 := rfl
example : repr256_le (String.toList "\x56\x34\x12\x00"    ) = 0x123456 := rfl
example : repr256_le (String.toList "\x56\x34\x12"        ) = 0x123456 := rfl

/-- `repr256_be a` returns `n`, if `a` is the big-endian representation of `n`. -/
def repr256_be (a : List Char) : Nat := repr256_le (List.reverse a)

example : repr256_be (String.toList "\x00\x00\x12\x34\x56") = 0x123456 := rfl
example : repr256_be (String.toList     "\x00\x12\x34\x56") = 0x123456 := rfl
example : repr256_be (String.toList         "\x12\x34\x56") = 0x123456 := rfl

/-- Lemma usable to drive induction via the base 256 representation of a Nat. -/
theorem base256_ind (P : Nat → Prop) (h0 : P 0) (hstep : ∀ (q r : Nat), r < 256 → P q → P (256 * q + r)) : ∀ n, P n := by
    intro n
    induction n using Nat.strongRecOn
    next n ih =>
      have hn : n = 256 * (n / 256) + (n % 256) := by omega
      rw [hn]
      apply (hstep (n / 256) (n % 256))
      · omega
      · match n with
        | 0     => assumption
        | p + 1 => apply ih; omega

/-- Lemma formalizing one step of the `itobs_be_loop` recursive function. -/
theorem itobs_be_loop_step (w : Nat) (a : List Char) (n : Nat) :
  itobs_be_loop (w + 1) a n = itobs_be_loop w (Char.ofNat (n % 256) :: a) (n / 256) := by induction w <;> simp [itobs_be_loop]

/-- Lemma formalizing the base case of the `itobs_be_loop` recursive function. -/
theorem itobs_be_loop_end (a : List Char) :
  itobs_be_loop 0 a 0 = .ok a := by simp [itobs_be_loop]; rfl

/-- Lemma formalizing the error base case of the `itobs_be_loop` recursive function. -/
theorem itobs_be_loop_end_error (a : List Char) (n : Nat) (hn : 0 < n) :
  itobs_be_loop 0 a n = .error "integerToByteString: cannot represent Integer in given number of bytes" := by
    unfold itobs_be_loop
    split
    · contradiction
    · contradiction
    · rfl

theorem itobs_be_loop_correct_l (w n : Nat) (a : List Char) (hwn : n < 256 ^ w) :
  itobs_be_loop w [] n = .ok a → repr256_be a = n := by sorry


theorem itobs_be_loop_correct_r (w n : Nat) (a : List Char) (hwn : n < 256 ^ w) :
  repr256_be a = n → itobs_be_loop w [] n = .ok a := by sorry

-- theorem

/-- Lemma formalizing the correctness of the `itobs_be_loop` recursive function. -/
theorem itobs_be_loop_correct (w n : Nat) (a : List Char) (hwn : n < 256 ^ w) :
  itobs_be_loop w [] n = .ok a ↔ repr256_be a = n := by
    constructor
    · apply itobs_be_loop_correct_l <;> assumption
    · apply itobs_be_loop_correct_r <;> assumption

/-- Lemma formalizing the error case for `itobs_be` and `itobs_le` in case `w < 0`. -/
theorem integerToByteString_neg_w (e : Bool) (w n : Integer) : w < 0 →
  integerToByteString e w n = .error "integerToByteString: negative length argument" := by
    intro hw
    simp
    split <;> rfl

/-- Lemma formalizing the error case for `itobs_be` and `itobs_le` in case `w > 8192`. -/
theorem integerToByteString_high_w (e : Bool) (w n : Integer) : w > 8192 →
  integerToByteString e w n = .error "integerToByteString: requested length is too long (maximum is 8192 bytes)" := by
    intro hw
    simp
    split
    · have h   : w < 0            := by assumption
      have h0  : 0 < (8192 : Int) := by simp
      have hn  : w < 8192         := Int.lt_trans h h0
      have hnw : ¬ w > 8192       := Int.lt_asymm hn
      contradiction
    · rfl

-- itobs_le (w, n) = itobs_be (w, n) = ×, if w < 0 or w > 8192
/-- Given `w` and `n`, if w < 0 or w > 8192, `integerToByteString` returns an error. -/
theorem integerToByteString_w_bounds_err (e : Bool) (w n : Integer) : w < 0 ∨ w > 8192 →
  (integerToByteString e w n |> Except.isError) := by
    intro hw
    cases hw with
    | inl hw => rw [integerToByteString_neg_w] ; rfl; assumption
    | inr hw => rw [integerToByteString_high_w]; rfl; assumption

/-- Lemma formalizing the error case for `itobs_be` and `itobs_le` in case `n < 0`. -/
theorem integerToByteString_neg_n (e : Bool) (w n : Integer) : 0 ≤ w → w ≤ 8192 → n < 0 →
  integerToByteString e w n = .error "integerToByteString: cannot convert negative Integer" := by
    intro hw0 hw8 hn
    simp [integerToByteString]
    split
    · have h : w < 0 := by assumption
      rw [←Int.not_le] at h
      contradiction
    · split
      · have h : 8192 < w := by assumption
        rw [←Int.not_le] at h
        contradiction
      · split
        · have h : w = 0 ∧ 65536 ≤ integerLog2 n := by assumption
          obtain ⟨hw, hlog2⟩ := h
          cases n with
          | ofNat n   => contradiction
          | negSucc n => simp [integerLog2] at hlog2
        · rfl

/-- Lemma formalizing the error case for `itobs_be` and `itobs_le` in case `n ≥ 2 ^ 65536`. -/
theorem integerToByteString_zero_w_high_n (e : Bool) (n : Integer) : n ≥ 2 ^ 65536 →
  integerToByteString e 0 n = .error "integerToByteString: input too long (maximum is 2^65536-1)" := by
    intros hn
    simp
    split
    · rfl
    · have h : ¬65536 ≤ integerLog2 n := by assumption
      cases n with
      | ofNat n =>
          simp [integerLog2] at h
          by_cases hn0 : n = 0
          · rw [hn0] at hn
            have h00      : Int.ofNat 0 = 0       := rfl
            have hpow2pos : (0 : Int) < 2 ^ 65536 := by apply Int.pow_pos; simp
            have hpow2neg : 2 ^ 65536 ≤ (0 : Int) := by rw [h00] at hn; apply hn
            exfalso
            apply Int.not_le_of_gt <;> omega
          · split
            · have h  : Int.ofNat n < 0 := by assumption
              have hn : 0 ≤ Int.ofNat n := by apply Int.ofNat_zero_le
              apply (False.elim (Int.not_le_of_gt  h hn ))
            · have hnlog2 : Nat.log2 n < 65536      := by omega
              have hnpow2 : n < 2 ^ 65536           := by rwa [Nat.log2_lt] at hnlog2; assumption
              have hipow2 : Int.ofNat n < 2 ^ 65536 := by rwa [←Int.ofNat_lt, ←Int.ofNat_eq_coe, Int.natCast_pow 2 65536] at hnpow2
              exfalso
              apply Int.not_le_of_gt <;> omega
      | negSucc n =>
          have hpow2neg : 2 ^ 65536 < (0 : Int) := by apply Int.lt_of_le_of_lt; assumption; simp
          have hpow2pos : (0 : Int) ≤ 2 ^ 65536 := by apply Int.pow_nonneg; simp
          exfalso
          apply Int.not_lt_of_ge <;> omega

/-- Lemma that shows that integerLog2 consistently adheres to the limits specified by the specs. -/
theorem integerWidth_integerLog2_max_consistent (n : Nat) :
  integerLog2 n < maxOutputBitsLength ↔ integerWidth n <= maxOutputLength := by
    constructor <;>
      (simp [maxOutputBitsLength, maxOutputLength, Nat.reduceMul, integerLog2]
       induction n <;> simp [integerWidth] ; omega)

/-- Helper lemma to be used later in rewrites. -/
theorem pow2_pow256 (n : Nat) : 2 ^ (n * 8) = 256 ^ n := by
  induction n
  next =>
    rfl
  next n ihn =>
    have h256 : 0 < 256 := by simp
    rwa [Nat.succ_mul, Nat.pow_add, Nat.pow_add, Nat.mul_right_cancel_iff h256]

/-- Helper lemma to be used later in rewrites. -/
theorem Int.eq_of_toNat (n m : Int) (hn : 0 ≤ n) (hm : 0 ≤ m) : n.toNat = m.toNat ↔ n = m := by
  constructor <;> omega

/-- Helper lemma to be used later in rewrites. -/
theorem pow2_pow256_int (n : Nat) : 2 ^ (n * 8) = (256 : Int) ^ n := by
  rw [←Int.eq_of_toNat] <;> try (apply Int.pow_nonneg; omega)
  · repeat (rw [Int.toNat_pow_of_nonneg]) <;> try omega
    simp [pow2_pow256]

/-- Helper lemma to be used later in rewrites. -/
theorem integerLog2_nat_le (n m : Nat) (h : 0 < m) : n ≤ integerLog2 m ↔ 2 ^ n ≤ m := by
  simp [integerLog2]
  apply Nat.le_log2
  rwa [Nat.ne_zero_iff_zero_lt]

/-- Helper lemma to be used later in rewrites. -/
theorem integerLog2_nat_int_le (n : Nat) (m : Int) (hm : 0 < m) : n ≤ integerLog2 m ↔ 2 ^ n ≤ m := by
  cases m with
  | ofNat m =>
      constructor <;> intro h
      · simp [integerLog2] at h
        simp
        rw [←Int.toNat_le, Int.toNat_pow_of_nonneg] <;> simp
        rwa [←integerLog2_nat_le]
        rwa [←Int.natCast_pos]
      · rw [Int.ofNat_eq_coe, integerLog2_nat_le]
        · rwa [←Int.ofNat_le, Lean.Omega.Int.ofNat_pow]
        · rwa [←Int.natCast_pos]
  | negSucc m => contradiction

/-- Helper lemma to be used later in rewrites. -/
theorem integerLog2_int_le (n m : Int) (hm : 0 < m) : n ≤ integerLog2 m ↔ 2 ^ Int.toNat n ≤ m := by
  cases n with
  | ofNat n =>
      constructor <;> intro h
      · rw [Int.ofNat_eq_coe, Int.toNat_natCast]
        rw [←integerLog2_nat_int_le]
        · rwa [←Int.ofNat_le]
        · assumption
      · rw [Int.ofNat_eq_coe, Int.ofNat_le]
        rw [integerLog2_nat_int_le]
        · rwa [←Int.toNat_natCast n]
        · assumption
  | negSucc n =>
      have h : Int.negSucc n ≤ integerLog2 m := Int.le.intro_sub (integerLog2 m + n.succ) rfl
      constructor <;> intro <;> assumption

/-- Helper lemma to be used later in rewrites. -/
theorem Int.pow_of_nonneg_min (z : Integer) (n : Nat) (hz : 0 < z) : 0 < z ^ n := by
  simp [HPow.hPow, Pow.pow, NatPow.pow]
  induction n
  next => simp [Int.pow]
  next n ih => simp [Int.pow]; apply Int.mul_pos <;> assumption

/-- Lemma characterizing `iobs_be` and `itobs_le` in the case when other bounds are adhered to,
    but `n` does not fit in `w` number of bytes. -/
theorem integerToByteString_nonzero_w_high_n (e : Bool) (w : Nat) (n : Integer) : 0 < w → w ≤ 8192 → n < 2 ^ 65536 → 256 ^ w ≤ n →
  integerToByteString e w n = .error "integerToByteString: cannot represent Integer in given number of bytes" := by
    intros hw0 hw8 hn hwn
    have hn0 : 0 < n := by
      apply Int.lt_of_lt_of_le (b := 256 ^ w)
      · apply Int.pow_of_nonneg_min (z := 256) (n := w)
        simp
      · apply hwn
    simp
    split
    next _ => clear hn; contradiction
    next _ =>
      split
      next h' => have h : 8192 < (w : Int) := h'; clear hn; omega
      next _ =>
        split
        next h => obtain ⟨h, _⟩ := h; clear hn; omega
        next _ =>
          split
          next h => exfalso; exact (Int.lt_asymm h hn0)
          next _ =>
            split
            next _               => exfalso; exact (Int.lt_irrefl 0 hn0)
            next n' _ hwe0 _ _   => clear hn; norm_cast at hwe0; omega
            next w' n' _ _ _ _ _ => sorry -- TODO: finish proof
            next _               => sorry -- TODO: finish proof

-- itobs_le (w, n) = itobs_be (w, n) = ×, if n < 0 or n ≥ 2 ^ 65536
/-- Given `w` and `n`, if n < 0 or n > 2 ^ 65536, `integerToByteString` returns an error. -/
theorem integerToByteString_n_bounds_err (e : Bool) (w n : Integer) : n < 0 ∨ n ≥ 2 ^ 65536 →
  (integerToByteString e w n |> Except.isError) := sorry

example : byteStringToInteger false "\x56\x34\x12\x00\x00" = 0x123456 := rfl
example : byteStringToInteger true  "\x00\x00\x12\x34\x56" = 0x123456 := rfl

theorem bstoi_itobs_roundtrip (e : Bool) (s : String) :
  integerToByteString e (byteStringToInteger e s) (String.length s) = .ok s := sorry

theorem itobs_bstoi_equivalence (e : Bool) (s : String) (w n : Integer) :
  integerToByteString e w n = .ok s → byteStringToInteger e s = n := sorry

theorem bstoi_itobs_equivalence (e : Bool) (s : String) (w n : Integer) :
  w = 0 ∨ String.length s ≤ w → byteStringToInteger e s = n → integerToByteString e w n = .ok s := sorry

example : andByteString true  "\xA5\xFF" "\x5A" = "\x00\xFF" := rfl
example : andByteString false "\xA5\xFF" "\x5A" = "\x00"     := rfl

-- TODO: formalizations for andByteString

example :  orByteString true  "\xA5\xFF" "\x5A" = "\xFF\xFF" := rfl
example :  orByteString false "\xA5\xFF" "\x5A" = "\xFF"     := rfl

-- TODO: formalizations for orByteString

example : xorByteString true  "\xAF\xFF" "\x5A" = "\xF5\xFF" := rfl
example : xorByteString false "\xAF\xFF" "\x5A" = "\xF5"     := rfl

-- TODO: formalizations for xorByteString

example : complementByteString "\xA5\x5F" = "\x5A\xA0" := by native_decide

-- TODO: formalizations for complementByteString

example : shiftByteString "\xA5\x5F"   1  = "\x4A\xBE" := rfl
example : shiftByteString "\xCA\xFE"   4  = "\xAF\xE0" := rfl
example : shiftByteString "\xCA\xFE" (-4) = "\x0C\xAF" := rfl

-- TODO: formalizations for shiftByteString

example : rotateByteString "\xA5\x5F"   1  = "\x4A\xBF" := rfl
example : rotateByteString "\xCA\xFE"   4  = "\xAF\xEC" := rfl
example : rotateByteString "\xCA\xFE" (-4) = "\xEC\xAF" := rfl

-- TODO: formalizations for rotateByteString

example : countSetBits "\xF0"     = 4 := rfl
example : countSetBits "\xA5"     = 4 := rfl
example : countSetBits "\xFF\x00" = 8 := rfl

-- TODO: formalizations for countSetBits

example : findFirstSetBit "\xF0"     = 4 := rfl
example : findFirstSetBit "\xFF\x00" = 8 := rfl
example : findFirstSetBit "\xFF\x01" = 0 := rfl

-- TODO: formalizations for firstSetBit

example : readBit "\xA5"      8 = .error "readBit: index out of bounds" := rfl
example : readBit "\xA5"      3 = .ok false                             := rfl
example : readBit "\xA5"      7 = .ok true                              := rfl
example : readBit "\xA5\x00"  3 = .ok false                             := rfl
example : readBit "\xA5\x00" 14 = .ok false                             := rfl
example : readBit "\xA5\x00" 15 = .ok true                              := rfl

-- TODO: formalizations for readBit

example : writeBit "\x00\x00"  0 true  = .ok "\x00\x01" := rfl
example : writeBit "\x00\x01"  0 true  = .ok "\x00\x01" := rfl
example : writeBit "\x00\x01" 15 true  = .ok "\x80\x01" := rfl
example : writeBit "\x80\x01"  0 false = .ok "\x80\x00" := rfl

-- TODO: formalizations for writeBit

example : writeBits "\x00\x00" [15, 13, 8, 10]    true  = .ok "\xA5\x00" := rfl
example : writeBits "\x00\x00" [15, 13, 8, 10]    false = .ok "\x00\x00" := rfl
example : writeBits "\xFF\xFF" [0, 13, 12, 8, 10] false = .ok "\xCA\xFE" := rfl

-- TODO: formalizations for writeBits

example : replicateByte    4 101 = .ok "eeee" := rfl
example : replicateByte (-4) 101 = .error "replicateByte: negative length requested" := rfl

theorem replicateByte_zero_l (b : Integer) : 0 ≤ b → b ≤ 255 → replicateByte 0 b = .ok "" := by
  intros hbi hbs
  simp [replicateByte]
  split
  next => contradiction
  next => contradiction
  next l b hl =>
    have hl : l = 0 := by grind only
    subst l
    simp
    split
    next h =>
      have hbs' : b ≤ 255 := by grind only
      omega
    next => rfl

-- TODO: formalizations for replicateByte

end PlutusCore.Bitwise
