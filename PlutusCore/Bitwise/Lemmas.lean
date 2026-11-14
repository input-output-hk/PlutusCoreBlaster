import PlutusCore.Bitwise.Basic

open PlutusCore.Integer
open PlutusCore.Bitwise.BitwiseInternal
open PlutusCore.Bytes (byteStr)

namespace PlutusCore.Bitwise

/-! ## Theorems on Logical and Bitwise builtin functions. -/

def Except.isError (e : Except ε α) : Bool := not (Except.isOk e)

-- itobs_loop (w, n) = ×, if 256 ^ w ≤ n
/-- Given `w` and `n`, if 256 ^ w ≤ n, `itobs_loop` returns an error -/
theorem itobs_loop_high_n (e : Bool) (w n : Nat) (a : String) (hwn : 256 ^ w ≤ n) :
  itobs_loop e w a n = .error "integerToByteString: cannot represent Integer in given number of bytes" := by
    induction w generalizing a n
    next =>
      unfold itobs_loop
      split <;> try contradiction
      rfl
    next p ih =>
      rw [itobs_loop, ih]
      rw [Nat.pow_succ] at hwn
      omega

/-- Lemma usable to drive induction via the base 256 representation of a Nat. -/
theorem Nat.base256_ind (P : Nat → Prop) (h0 : P 0) (hstep : ∀ (q r : Nat), r < 256 → P q → P (256 * q + r)) : ∀ n, P n := by
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

/-- Lemma formalizing one step of the `itobs_loop` recursive function. -/
theorem itobs_loop_step (e : Bool) (w : Nat) (a : String) (n : Nat) :
  itobs_loop e (w + 1) a n =
    itobs_loop e w (if e then byteStr (n % 256) ++ a else a ++ byteStr (n % 256)) (n / 256) := by
  rw [itobs_loop]

/-- Lemma formalizing the base case of the `itobs_loop` recursive function. -/
theorem itobs_loop_end (e : Bool) (a : String) :
  itobs_loop e 0 a 0 = .ok a := by simp [itobs_loop]; rfl

/-- Lemma formalizing the error base case of the `itobs_loop` recursive function. -/
theorem itobs_loop_end_error (e : Bool) (a : String) (n : Nat) (hn : 0 < n) :
  itobs_loop e 0 a n = .error "integerToByteString: cannot represent Integer in given number of bytes" := by
    unfold itobs_loop
    split
    · contradiction
    · contradiction
    · rfl

theorem String.append_unchanged_empty_r (s1 s2 : String) :
  s1 = s1 ++ s2 → s2 = "" :=
    by
      let ⟨c1⟩ := s1
      let ⟨c2⟩ := s2
      induction c1 generalizing c2 with
      | cons h1 t1 ih1 =>
          simp [HAppend.hAppend, Append.append]
          unfold String.append
          simp; intro hc2; subst hc2; rfl
      | nil => simp; intro h; symm; assumption

/-- Multiplying every term of the sum `repr256_le` takes by 256 multiplies the sum by 256. -/
theorem sum_mapIdx_mul_256 (l : List Char) (f : Nat → Nat) :
  (l.mapIdx (fun i c => c.toNat * (256 * f i))).sum = 256 * (l.mapIdx (fun i c => c.toNat * f i)).sum :=
    by
      induction l generalizing f with
      | nil => rfl
      | cons c l ih =>
          rw [List.mapIdx_cons, List.mapIdx_cons, List.sum_cons, List.sum_cons, ih (fun i => f (i + 1)),
              Nat.mul_add, Nat.mul_left_comm]

/-- The little-endian value of `c :: l` is `c` plus 256 times the value of `l`. -/
theorem repr256_le_cons (c : Char) (l : List Char) :
  repr256_le (c :: l) = c.toNat + 256 * repr256_le l :=
    by
      unfold repr256_le
      simp only [List.mapIdx_cons, List.sum_cons, Nat.pow_zero, Nat.mul_one, Nat.pow_succ']
      rw [sum_mapIdx_mul_256 l (fun i => 256 ^ i)]

/-- The big-endian value of `l ++ [c]` is `c` plus 256 times the value of `l`. -/
theorem repr256_be_append_singleton (l : List Char) (c : Char) :
  repr256_be (l ++ [c]) = c.toNat + 256 * repr256_be l :=
    by
      rw [repr256_be, repr256_be, List.reverse_append]
      exact repr256_le_cons c l.reverse

/-- When the big-endian `itobs_loop` succeeds, it has put the big-endian digits of `n` in front
    of `acc`. -/
theorem itobs_be_loop_ok (w n : Nat) (acc r : String) (hwn : n < 256 ^ w) :
  itobs_loop true w acc n = .ok r → ∃ b : String, r = b ++ acc ∧ repr256_be b.data = n :=
    by
      induction w generalizing n acc with
      | zero =>
          intro h
          cases n with
          | zero =>
              rw [itobs_loop_end] at h
              cases h
              exact ⟨"", (String.empty_append _).symm, rfl⟩
          | succ n => rw [Nat.pow_zero] at hwn; omega
      | succ w ih =>
          intro h
          rw [itobs_loop_step, if_pos rfl] at h
          have hq : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by rwa [← Nat.pow_succ])
          have hr : n % 256 < 256 := Nat.mod_lt _ (by decide)
          obtain ⟨b, hrb, hb⟩ := ih (n / 256) (byteStr (n % 256) ++ acc) hq h
          refine ⟨b ++ byteStr (n % 256), by rw [hrb, String.append_assoc], ?_⟩
          rw [String.data_append, PlutusCore.Bytes.byteStr_eq _ hr]
          show repr256_be (b.data ++ [Char.ofNat (n % 256)]) = n
          rw [repr256_be_append_singleton, PlutusCore.Bytes.toNat_ofNat_byte _ hr, hb]
          omega

/-- The big-endian `itobs_loop` puts its bytes in front of the accumulator, so a result
    `a ++ acc` means that `a` is the big-endian representation of `n`. -/
theorem itobs_be_loop_correct_acc (w n : Nat) (a acc : String) (hwn : n < 256 ^ w) :
  itobs_loop true w acc n = .ok (a ++ acc) → repr256_be a.data = n :=
    by
      intro h
      obtain ⟨b, hab, hb⟩ := itobs_be_loop_ok w n acc (a ++ acc) hwn h
      have hd := congrArg String.data hab
      rw [String.data_append, String.data_append] at hd
      rw [String.ext (List.append_cancel_right hd)]
      exact hb

/-- When the little-endian `itobs_loop` succeeds, it has put the little-endian digits of `n` after
    `acc`. -/
theorem itobs_le_loop_ok (w n : Nat) (acc r : String) (hwn : n < 256 ^ w) :
  itobs_loop false w acc n = .ok r → ∃ b : String, r = acc ++ b ∧ repr256_le b.data = n :=
    by
      induction w generalizing n acc with
      | zero =>
          intro h
          cases n with
          | zero =>
              rw [itobs_loop_end] at h
              cases h
              exact ⟨"", (String.append_empty _).symm, rfl⟩
          | succ n => rw [Nat.pow_zero] at hwn; omega
      | succ w ih =>
          intro h
          rw [itobs_loop_step, if_neg Bool.false_ne_true] at h
          have hq : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by rwa [← Nat.pow_succ])
          have hr : n % 256 < 256 := Nat.mod_lt _ (by decide)
          obtain ⟨b, hrb, hb⟩ := ih (n / 256) (acc ++ byteStr (n % 256)) hq h
          refine ⟨byteStr (n % 256) ++ b, by rw [hrb, String.append_assoc], ?_⟩
          rw [String.data_append, PlutusCore.Bytes.byteStr_eq _ hr]
          show repr256_le (Char.ofNat (n % 256) :: b.data) = n
          rw [repr256_le_cons, PlutusCore.Bytes.toNat_ofNat_byte _ hr, hb]
          omega

/-- `itobs_loop` fails unless `n < 256 ^ w`. -/
theorem itobs_loop_lt_of_ok (e : Bool) (w n : Nat) (acc r : String) :
  itobs_loop e w acc n = .ok r → n < 256 ^ w :=
    by
      intro h
      apply Nat.lt_of_not_le
      intro hwn
      rw [itobs_loop_high_n e w n acc hwn] at h
      cases h

theorem itobs_be_loop_correct_l (w n : Nat) (a : String) (hwn : n < 256 ^ w) :
  itobs_loop true w "" n = .ok a → repr256_be a.data = n :=
    by
      intro h
      exact itobs_be_loop_correct_acc w n a "" hwn (by rw [String.append_empty]; exact h)

/-- Given the value and the number of the bytes of `r`, little-endian, the big-endian `itobs_loop`
    writes them in front of `acc`, most significant first. -/
theorem itobs_be_loop_repr (r : List Char) (acc : String) (hr : ∀ c ∈ r, c.toNat < 256) :
  itobs_loop true r.length acc (repr256_le r) = .ok (⟨r.reverse⟩ ++ acc) :=
    by
      induction r generalizing acc with
      | nil =>
          show itobs_loop true 0 acc 0 = .ok ("" ++ acc)
          rw [String.empty_append, itobs_loop_end]
      | cons c r ih =>
          have hc : c.toNat < 256 := hr c List.mem_cons_self
          have hq : (c.toNat + 256 * repr256_le r) / 256 = repr256_le r := by omega
          have hm : (c.toNat + 256 * repr256_le r) % 256 = c.toNat := by omega
          rw [List.length_cons, repr256_le_cons, itobs_loop_step, if_pos rfl, hq, hm,
              PlutusCore.Bytes.byteStr_eq _ hc, Char.ofNat_toNat,
              ih _ (fun d hd => hr d (List.mem_cons_of_mem c hd)), List.reverse_cons, ← String.append_assoc]
          rfl

/-- Given the value and the number of the bytes of `r`, little-endian, the little-endian
    `itobs_loop` writes them after `acc`, least significant first. -/
theorem itobs_le_loop_repr (r : List Char) (acc : String) (hr : ∀ c ∈ r, c.toNat < 256) :
  itobs_loop false r.length acc (repr256_le r) = .ok (acc ++ ⟨r⟩) :=
    by
      induction r generalizing acc with
      | nil =>
          show itobs_loop false 0 acc 0 = .ok (acc ++ "")
          rw [String.append_empty, itobs_loop_end]
      | cons c r ih =>
          have hc : c.toNat < 256 := hr c List.mem_cons_self
          have hq : (c.toNat + 256 * repr256_le r) / 256 = repr256_le r := by omega
          have hm : (c.toNat + 256 * repr256_le r) % 256 = c.toNat := by omega
          rw [List.length_cons, repr256_le_cons, itobs_loop_step, if_neg Bool.false_ne_true, hq, hm,
              PlutusCore.Bytes.byteStr_eq _ hc, Char.ofNat_toNat,
              ih _ (fun d hd => hr d (List.mem_cons_of_mem c hd)), String.append_assoc]
          rfl

/-- `itobs_loop` writes back the bytes of `s`, given their value and their number. -/
theorem itobs_loop_repr (e : Bool) (s : String) (hs : ∀ c ∈ s.data, c.toNat < 256) :
  itobs_loop e s.length "" (if e then repr256_be s.data else repr256_le s.data) = .ok s :=
    by
      cases e with
      | false =>
          have h := itobs_le_loop_repr s.data "" hs
          rw [String.empty_append] at h
          exact h
      | true =>
          have h := itobs_be_loop_repr s.data.reverse "" (fun c hc => hs c (List.mem_reverse.mp hc))
          rw [List.length_reverse, List.reverse_reverse, String.append_empty] at h
          exact h

/-- The converse of `itobs_be_loop_correct_l`, for a string `a` of `w` bytes. -/
theorem itobs_be_loop_correct_r (w n : Nat) (a : String) (hlen : a.length = w)
    (hbytes : ∀ c ∈ a.data, c.toNat < 256) :
  repr256_be a.data = n → itobs_loop true w "" n = .ok a :=
    by
      intro h
      subst hlen h
      exact itobs_loop_repr true a hbytes

-- theorem

/-- Lemma formalizing the correctness of the big-endian `itobs_loop`, for a string `a` of `w`
    bytes. -/
theorem itobs_be_loop_correct (w n : Nat) (a : String) (hwn : n < 256 ^ w) (hlen : a.length = w)
    (hbytes : ∀ c ∈ a.data, c.toNat < 256) :
  itobs_loop true w "" n = .ok a ↔ repr256_be a.data = n := by
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

/-- `integerToByteString` on natural numbers within the limits runs `itobs_loop`, with the width
    `integerWidth n` when `w = 0`. -/
theorem integerToByteString_ofNat (e : Bool) (w n : Nat) (hw : w ≤ 8192)
    (hlog : w = 0 → Nat.log2 n < 65536) :
  integerToByteString e w n = itobs_loop e (if w = 0 then integerWidth n else w) "" n :=
    by
      have h1 : ¬ ((w : Int) < 0) := by omega
      have h2 : ¬ ((w : Int) > (maxOutputLength : Nat)) := by simp only [maxOutputLength]; omega
      have h3 : ¬ ((w : Int) = 0 ∧ integerLog2 (n : Int) ≥ maxOutputBitsLength) := by
        intro ⟨h3, h4⟩
        simp only [integerLog2, maxOutputBitsLength, maxOutputLength] at h4
        have := hlog (by omega)
        omega
      have h4 : ¬ ((n : Int) < 0) := by omega
      unfold integerToByteString
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      cases w with
      | zero =>
          cases n with
          | zero => rfl
          | succ k => rfl
      | succ j => rfl

/-- When `integerToByteString` succeeds, its arguments are natural numbers within the limits, and
    the result is that of `itobs_loop`. -/
theorem integerToByteString_ok (e : Bool) (w n : Integer) (s : String) :
  integerToByteString e w n = .ok s →
    ∃ w' n' : Nat, w = w' ∧ n = n' ∧ w' ≤ 8192 ∧ (w' = 0 → Nat.log2 n' < 65536) ∧
      itobs_loop e (if w' = 0 then integerWidth n' else w') "" n' = .ok s :=
    by
      intro h
      have h' := h
      unfold integerToByteString at h'
      split at h'; · cases h'
      split at h'; · cases h'
      split at h'; · cases h'
      split at h'; · cases h'
      rename_i hw0 hwm hwn hn0
      obtain ⟨w', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.not_lt.mp hw0)
      obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.not_lt.mp hn0)
      have hwm' : ¬ ((w' : Int) > 8192) := hwm
      have hw : w' ≤ 8192 := by omega
      have hlog : w' = 0 → Nat.log2 n' < 65536 :=
        fun h0 => Nat.lt_of_not_le fun hge => hwn ⟨by rw [h0]; rfl, hge⟩
      rw [integerToByteString_ofNat e w' n' hw hlog] at h
      exact ⟨w', n', rfl, rfl, hw, hlog, h⟩

/-- Lemma characterizing `iobs_be` and `itobs_le` in the case when other bounds are adhered to,
    but `n` does not fit in `w` number of bytes. -/
theorem integerToByteString_nonzero_w_high_n (e : Bool) (w : Nat) (n : Integer) : 0 < w → w ≤ 8192 → n < 2 ^ 65536 → 256 ^ w ≤ n →
  integerToByteString e w n = .error "integerToByteString: cannot represent Integer in given number of bytes" := by
    intro hw0 hw8 _ hwn
    have hn0 : 0 < n := by
      apply Int.lt_of_lt_of_le (b := 256 ^ w)
      · apply Int.pow_of_nonneg_min (z := 256) (n := w)
        simp
      · apply hwn
    obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hn0)
    rw [integerToByteString_ofNat e w n' hw8 (fun h => absurd h (by omega)), if_neg (by omega)]
    apply itobs_loop_high_n
    have h : ((256 ^ w : Nat) : Int) ≤ (n' : Int) := by rw [Int.natCast_pow]; exact hwn
    exact Int.ofNat_le.mp h

-- itobs_le (w, n) = itobs_be (w, n) = ×, if n < 0 or n ≥ 2 ^ 65536
/-- Given `w` and `n`, if n < 0 or n > 2 ^ 65536, `integerToByteString` returns an error. -/
theorem integerToByteString_n_bounds_err (e : Bool) (w n : Integer) : n < 0 ∨ n ≥ 2 ^ 65536 →
  (integerToByteString e w n |> Except.isError) :=
    by
      intro hn
      cases hr : integerToByteString e w n with
      | error _ => rfl
      | ok s =>
          exfalso
          obtain ⟨w', n', -, rfl, hw, hlog, h⟩ := integerToByteString_ok e w n s hr
          have hW : (if w' = 0 then integerWidth n' else w') ≤ 8192 := by
            split
            · next h0 => exact (integerWidth_integerLog2_max_consistent n').mp (hlog h0)
            · exact hw
          have hlt : n' < 2 ^ 65536 := by
            have hpow := Nat.pow_le_pow_right (n := 2) (j := 65536) (by decide)
              (show 8 * (if w' = 0 then integerWidth n' else w') ≤ 65536 by omega)
            rw [Nat.pow_mul] at hpow
            exact Nat.lt_of_lt_of_le (itobs_loop_lt_of_ok e _ n' "" s h) hpow
          cases hn with
          | inl h =>
              have h' : ¬ ((n' : Int) < 0) := by omega
              exact h' h
          | inr h =>
              -- The exponent is generalised so that nothing tries to evaluate `2 ^ 65536`.
              revert hlt h
              generalize 65536 = k
              intro hlt h
              have h' : ((2 ^ k : Nat) : Int) ≤ (n' : Int) := by rw [Int.natCast_pow]; exact h
              exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (Int.ofNat_le.mp h'))

/-- The big-endian loop is a left fold over the characters, as `byteStringToInteger` was before it
    read through `PlutusCore.Bytes.uncons`. -/
theorem bstoi_be_loop_eq_foldl (n : Nat) (s : String) (acc : Nat) (h : s.length ≤ n) :
    bstoi_be_loop n s acc = s.data.foldl (fun acc c => acc * 256 + c.toNat) acc := by
  induction n generalizing s acc with
  | zero =>
    obtain ⟨l⟩ := s
    cases l with
    | nil => rfl
    | cons c cs => simp [String.length] at h
  | succ n ih =>
    obtain ⟨l⟩ := s
    cases l with
    | nil => rw [bstoi_be_loop, PlutusCore.Bytes.uncons_nil]; rfl
    | cons c cs =>
      rw [bstoi_be_loop, PlutusCore.Bytes.uncons_cons]
      exact ih ⟨cs⟩ _ (by simp [String.length] at h ⊢; omega)

/-- The little-endian loop is a right fold over the characters. -/
theorem bstoi_le_loop_eq_foldr (n : Nat) (s : String) (h : s.length ≤ n) :
    bstoi_le_loop n s = s.data.foldr (fun c acc => c.toNat + 256 * acc) 0 := by
  induction n generalizing s with
  | zero =>
    obtain ⟨l⟩ := s
    cases l with
    | nil => rfl
    | cons c cs => simp [String.length] at h
  | succ n ih =>
    obtain ⟨l⟩ := s
    cases l with
    | nil => rw [bstoi_le_loop, PlutusCore.Bytes.uncons_nil]; rfl
    | cons c cs =>
      rw [bstoi_le_loop, PlutusCore.Bytes.uncons_cons]
      dsimp only
      rw [ih ⟨cs⟩ (by simp [String.length] at h ⊢; omega)]
      rfl

/-- `byteStringToInteger` computes the `Char`-list folds it computed before it read through
    `PlutusCore.Bytes.uncons`, on every string. -/
theorem byteStringToInteger_eq_foldl (e : Bool) (s : String) :
    byteStringToInteger e s =
    if e then .ofNat (s.data.foldl (fun acc c => acc * 256 + c.toNat) 0)
         else .ofNat (s.data.reverse.foldl (fun acc c => acc * 256 + c.toNat) 0) := by
  unfold byteStringToInteger
  rw [bstoi_be_loop_eq_foldl _ _ _ (Nat.le_refl _), bstoi_le_loop_eq_foldr _ _ (Nat.le_refl _),
      List.foldl_reverse]
  congr 2
  apply congrArg (fun f => List.foldr f 0 s.data)
  funext c acc
  omega

-- `byteStringToInteger` reads through the sealed `PlutusCore.Bytes.uncons`, which plain `rfl` does not unfold.
example : byteStringToInteger false "\x56\x34\x12\x00\x00" = 0x123456 := by with_unfolding_all rfl
example : byteStringToInteger true  "\x00\x00\x12\x34\x56" = 0x123456 := by with_unfolding_all rfl

/-- The little-endian value of a list is the right fold that `bstoi_le_loop` computes. -/
theorem repr256_le_eq_foldr (l : List Char) :
  repr256_le l = l.foldr (fun c acc => c.toNat + 256 * acc) 0 :=
    by
      induction l with
      | nil => rfl
      | cons c l ih => rw [repr256_le_cons, ih]; rfl

/-- `byteStringToInteger` computes the value of the bytes, in the order `e` gives. -/
theorem byteStringToInteger_eq_repr (e : Bool) (s : String) :
  byteStringToInteger e s = .ofNat (if e then repr256_be s.data else repr256_le s.data) :=
    by
      unfold byteStringToInteger
      rw [bstoi_be_loop_eq_foldl _ _ _ (Nat.le_refl _), bstoi_le_loop_eq_foldr _ _ (Nat.le_refl _),
          repr256_be, repr256_le_eq_foldr, repr256_le_eq_foldr, List.foldr_reverse]
      cases e
      · rfl
      · show Int.ofNat _ = Int.ofNat _
        congr 1
        apply congrArg (fun f => List.foldl f 0 s.data)
        funext acc c
        omega

/-- A string of at most 8192 bytes converts back to itself from its length and its value. -/
theorem bstoi_itobs_roundtrip (e : Bool) (s : String) (hs : ∀ c ∈ s.data, c.toNat < 256)
    (hlen : s.length ≤ 8192) :
  integerToByteString e (String.length s) (byteStringToInteger e s) = .ok s :=
    by
      rw [byteStringToInteger_eq_repr, Int.ofNat_eq_coe]
      by_cases h0 : s.length = 0
      · have hs0 : s = "" := String.ext (List.eq_nil_of_length_eq_zero (l := s.data) h0)
        subst hs0
        have hN : (if e then repr256_be "".data else repr256_le "".data) = 0 := by cases e <;> rfl
        rw [hN, integerToByteString_ofNat e _ 0 hlen (fun _ => by rw [Nat.log2_zero]; decide)]
        rfl
      · rw [integerToByteString_ofNat e _ _ hlen (fun h => absurd h h0), if_neg h0]
        exact itobs_loop_repr e s hs

theorem itobs_bstoi_equivalence (e : Bool) (s : String) (w n : Integer) :
  integerToByteString e w n = .ok s → byteStringToInteger e s = n :=
    by
      intro h
      obtain ⟨w', n', -, rfl, -, -, h⟩ := integerToByteString_ok e w n s h
      have hwn := itobs_loop_lt_of_ok e _ n' "" s h
      rw [byteStringToInteger_eq_repr, Int.ofNat_eq_coe]
      congr 1
      cases e with
      | false =>
          obtain ⟨b, rfl, hb⟩ := itobs_le_loop_ok _ n' "" s hwn h
          rw [String.empty_append]
          exact hb
      | true =>
          obtain ⟨b, rfl, hb⟩ := itobs_be_loop_ok _ n' "" s hwn h
          rw [String.append_empty]
          exact hb

/-- A string of at most 8192 bytes is what `integerToByteString` gives for its value, with its own
    length as the width, or with width 0 if it has no leading zero byte (as `integerWidth` says). -/
theorem bstoi_itobs_equivalence (e : Bool) (s : String) (w n : Integer)
    (hs : ∀ c ∈ s.data, c.toNat < 256) (hlen : s.length ≤ 8192) :
  w = String.length s ∨ (w = 0 ∧ String.length s = integerWidth n.toNat) →
    byteStringToInteger e s = n → integerToByteString e w n = .ok s :=
    by
      intro hw hn
      subst hn
      rcases hw with rfl | ⟨rfl, hW⟩
      · exact bstoi_itobs_roundtrip e s hs hlen
      · rw [byteStringToInteger_eq_repr, Int.ofNat_eq_coe, Int.toNat_natCast] at hW
        rw [byteStringToInteger_eq_repr, Int.ofNat_eq_coe,
            show (0 : Integer) = ((0 : Nat) : Integer) from rfl,
            integerToByteString_ofNat e 0 _ (by decide) ?_, if_pos rfl, ← hW]
        · exact itobs_loop_repr e s hs
        · intro _
          exact (integerWidth_integerLog2_max_consistent _).mpr (by rw [← hW]; exact hlen)

-- TODO: formalizations for writeBits

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

/-- `replicateByte` builds the `Char` list it built before it wrote bytes with
    `PlutusCore.Bytes.repB`. -/
theorem replicateByte_eq_replicate (l b : Nat) (hl : l ≤ maxOutputLength) (hb : b ≤ 255) :
    replicateByte (.ofNat l) (.ofNat b) = .ok ⟨List.replicate l (Char.ofNat b)⟩ := by
  rw [replicateByte, if_neg (Nat.not_lt.mpr hl), if_neg (Nat.not_lt.mpr hb),
      PlutusCore.Bytes.repB_eq l b (Nat.lt_succ_of_le hb)]
  rfl

-- TODO: formalizations for replicateByte

end PlutusCore.Bitwise
