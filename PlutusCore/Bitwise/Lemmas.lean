import PlutusCore.Bitwise.Basic

open PlutusCore.Integer
open PlutusCore.Bitwise.BitwiseInternal

namespace PlutusCore.Bitwise

/-! ## Theorems on Logical and Bitwise builtin functions. -/

def Except.isError (e : Except ε α) : Bool := not (Except.isOk e)

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

/-- Helper lemma: `Char.ofNat` is the identity on byte values. -/
theorem Char.toNat_ofNat_of_lt (k : Nat) (hk : k < 256) : (Char.ofNat k).toNat = k := by
  have hv : k.isValidChar := by simp [Nat.isValidChar]; omega
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

/-- `repr256_be` peels off the most significant byte. -/
theorem repr256_be_cons (c : Char) (a : List Char) :
  repr256_be (c :: a) = c.toNat * 256 ^ a.length + repr256_be a :=
    by
      simp [repr256_be, repr256_le, List.mapIdx_append, List.sum_append_nat]
      omega

/-- `bstoi_be_loop` computes `repr256_be`, shifted by the accumulator. -/
theorem bstoi_be_loop_eq (a : List Char) (acc : Nat) :
  bstoi_be_loop a acc = acc * 256 ^ a.length + repr256_be a :=
    by
      induction a generalizing acc with
      | nil         => simp [bstoi_be_loop, repr256_be, repr256_le]
      | cons c t ih =>
          rw [bstoi_be_loop, ih, repr256_be_cons, List.length_cons, Nat.pow_succ, Nat.add_mul,
              Nat.mul_assoc, Nat.mul_comm 256, Nat.add_assoc]

theorem bstoi_be_loop_append (a b : List Char) (acc : Nat) :
  bstoi_be_loop (a ++ b) acc = bstoi_be_loop b (bstoi_be_loop a acc) :=
    by
      induction a generalizing acc with
      | nil => rfl
      | cons c t ih => exact ih _

theorem repr256_be_eq_bstoi (a : List Char) : repr256_be a = bstoi_be_loop a 0 := by
  simp [bstoi_be_loop_eq]

/-- `repr256_be` peels off the least significant byte. -/
theorem repr256_be_concat (a : List Char) (c : Char) :
  repr256_be (a ++ [c]) = repr256_be a * 256 + c.toNat :=
    by
      simp [repr256_be_eq_bstoi, bstoi_be_loop_append, bstoi_be_loop]

/-- A sequence of `k` bytes represents a number below `256 ^ k`. -/
theorem repr256_be_lt (a : List Char) (ha : ∀ c ∈ a, c.toNat < 256) :
  repr256_be a < 256 ^ a.length :=
    by
      induction a with
      | nil => simp [repr256_be, repr256_le]
      | cons c t ih =>
        rw [repr256_be_cons, List.length_cons, Nat.pow_succ]
        have hc : c.toNat < 256 := ha c (by simp)
        have ht : repr256_be t < 256 ^ t.length := ih (fun x hx => ha x (by simp [hx]))
        have : c.toNat * 256 ^ t.length + 256 ^ t.length ≤ 256 ^ t.length * 256 := by
          rw [← Nat.succ_mul, Nat.mul_comm]; exact Nat.mul_le_mul_left _ hc
        omega

/-- A successful `itobs_be_loop` prepends exactly `w` bytes, which represent `n`. -/
theorem itobs_be_loop_ok (w : Nat) (acc r : List Char) (n : Nat) :
  itobs_be_loop w acc n = .ok r →
  ∃ d, r = d ++ acc ∧ d.length = w ∧ (∀ c ∈ d, c.toNat < 256) ∧ repr256_be d = n :=
    by
      induction w generalizing acc n with
      | zero =>
        intro h
        cases n with
        | zero =>
            rw [itobs_be_loop_end] at h
            cases h
            exact ⟨[], rfl, rfl, by simp, rfl⟩
        | succ k =>
            rw [itobs_be_loop_end_error _ _ (Nat.succ_pos k)] at h
            contradiction
      | succ w ih =>
          intro h
          rw [itobs_be_loop_step] at h
          obtain ⟨d, hr, hlen, hbytes, hrepr⟩ := ih _ _ h
          have hc : (Char.ofNat (n % 256)).toNat = n % 256 :=
            Char.toNat_ofNat_of_lt _ (Nat.mod_lt _ (by decide))
          refine ⟨d ++ [Char.ofNat (n % 256)], by simp [hr], by simp [hlen], ?_, ?_⟩
          · intro c hc'
            simp only [List.mem_append, List.mem_singleton] at hc'
            cases hc' with
            | inl h => exact hbytes c h
            | inr h => subst h; rw [hc]; exact Nat.mod_lt _ (by decide)
          · rw [repr256_be_concat, hrepr, hc]; omega

/-- `itobs_be_loop` reproduces any byte sequence from the number it represents. -/
theorem itobs_be_loop_repr (d acc : List Char) (hd : ∀ c ∈ d, c.toNat < 256) :
  itobs_be_loop d.length acc (repr256_be d) = .ok (d ++ acc) :=
    by
      generalize hw : d.length = w
      induction w generalizing d acc with
      | zero => rw [List.length_eq_zero_iff] at hw; subst hw; rfl
      | succ w ih =>
          rcases List.eq_nil_or_concat d with h | ⟨d, c, h⟩
          · subst h; contradiction
          subst h
          rw [List.concat_eq_append] at hd hw ⊢
          simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hw
          have hc : c.toNat < 256 := hd c (by simp)
          rw [itobs_be_loop_step, repr256_be_concat]
          have h1 : (repr256_be d * 256 + c.toNat) % 256 = c.toNat := by omega
          have h2 : (repr256_be d * 256 + c.toNat) / 256 = repr256_be d := by omega
          rw [h1, h2, Char.ofNat_toNat, ih d _ (fun x hx => hd x (by simp [hx])) hw]
          simp

theorem itobs_be_loop_correct_l (w n : Nat) (a : List Char) :
  itobs_be_loop w [] n = .ok a → repr256_be a = n :=
    by
      intro h
      obtain ⟨d, hr, _, _, hrepr⟩ := itobs_be_loop_ok w [] a n h
      rw [List.append_nil] at hr
      rwa [hr]

/-- `a` must consist of exactly `w` byte-valued characters: `itobs_be_loop` always emits `w`
    bytes, so e.g. `a = []` represents `0` but `itobs_be_loop 1 [] 0 = .ok ['\x00']`. -/
theorem itobs_be_loop_correct_r (w n : Nat) (a : List Char) (hlen : a.length = w) (hbytes : ∀ c ∈ a, c.toNat < 256) :
  repr256_be a = n → itobs_be_loop w [] n = .ok a :=
    by
      intro h
      subst hlen h
      rw [itobs_be_loop_repr a [] hbytes, List.append_nil]

/-- Lemma formalizing the correctness of the `itobs_be_loop` recursive function. -/
theorem itobs_be_loop_correct (w n : Nat) (a : List Char) (hlen : a.length = w) (hbytes : ∀ c ∈ a, c.toNat < 256) :
  itobs_be_loop w [] n = .ok a ↔ repr256_be a = n :=
    by
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
            next w' n' _ _ heq _ _ =>
              have hw' : w = w' := Int.ofNat.inj heq
              subst hw'
              have hwn' : 256 ^ w ≤ n' := by
                have h : ((256 ^ w : Nat) : Int) ≤ ((n' : Nat) : Int) := by rw [Int.natCast_pow]; exact hwn
                exact Int.ofNat_le.mp h
              rw [itobs_be_loop_high_n w n' [] hwn']
              rfl
            next m _ _ _ _ h _ _ =>
              exact (h w m.toNat rfl (Int.toNat_of_nonneg (Int.le_of_lt hn0)).symm).elim

/-- Helper lemma: moves a bound `2 ^ k ≤ n` from `Int` to `Nat` without evaluating `2 ^ k`
    (the kernel unfolds `Int.pow` one step per exponent, so `omega` chokes on `(2 : Int) ^ 65536`). -/
theorem Int.two_pow_le_natCast (k n : Nat) : (2 : Int) ^ k ≤ (n : Int) ↔ 2 ^ k ≤ n :=
  by
    rw [← Int.ofNat_le, Int.natCast_pow]
    rfl

/-- Within the length bounds, `integerToByteString` is a single `itobs_be_loop` run (of width
    `integerWidth n` when `w = 0`) followed by the byte-order selection. -/
theorem integerToByteString_nat (e : Bool) (w n : Nat) (hw8 : w ≤ 8192) (hwn : w = 0 → n < 2 ^ 65536) :
  integerToByteString e w n =
    (itobs_be_loop (if w = 0 then integerWidth n else w) [] n >>=
      fun r => if e then pure ⟨r⟩ else pure ⟨r.reverse⟩) :=
        by
          simp only [integerToByteString, maxOutputLength, maxOutputBitsLength]
          have h1 : ¬ ((w : Int) < 0) := by omega
          have h2 : ¬ ((w : Int) > ((8192 : Nat) : Int)) := by omega
          have h3 : ¬ ((w : Int) = 0 ∧ integerLog2 (n : Int) ≥ 8 * 8192) := by
            intro ⟨hw0, hlog⟩
            have hn := hwn (by omega)
            change Nat.log2 n ≥ 8 * 8192 at hlog
            by_cases hn0 : n = 0
            · subst hn0; rw [Nat.log2_zero] at hlog; omega
            · have := (Nat.log2_lt (k := 65536) hn0).mpr hn
              omega
          have h4 : ¬ ((n : Int) < 0) := by omega
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          split
          next _ _ heqw heqn =>
            have hw : w = 0 := Int.ofNat.inj heqw
            have hn : n = 0 := Int.ofNat.inj heqn
            subst hw hn
            rfl
          next _ _ n' _ heqw heqn =>
            have hw : w = 0 := Int.ofNat.inj heqw
            have hn : n = n' := Int.ofNat.inj heqn
            subst hw hn
            rfl
          next _ _ w' n' _ hw0 heqw heqn =>
            have hw : w = w' := Int.ofNat.inj heqw
            have hn : n = n' := Int.ofNat.inj heqn
            subst hw hn
            rw [if_neg hw0]
          next _ _ _ _ h =>
            exact (h w n rfl rfl).elim

/-- `byteStringToInteger` reads the big-endian byte sequence selected by `e`. -/
theorem byteStringToInteger_eq (e : Bool) (s : String) :
  byteStringToInteger e s = ((repr256_be (if e then s.data else s.data.reverse) : Nat) : Integer) :=
    by cases e <;> simp [byteStringToInteger, bstoi_be_loop_eq]

/-- Whatever `integerToByteString` produces reads back as the number it was given. -/
theorem itobs_post_ok (e : Bool) (k m : Nat) (s : String) :
  (itobs_be_loop k [] m >>= fun r => if e then pure ⟨r⟩ else pure ⟨r.reverse⟩) = (.ok s : Except String String)
  → byteStringToInteger e s = m :=
    by
      intro h
      cases hl : itobs_be_loop k [] m with
      | error _ => rw [hl] at h; contradiction
      | ok r =>
        rw [hl] at h
        obtain ⟨d, hr, _, _, hrepr⟩ := itobs_be_loop_ok k [] r m hl
        rw [List.append_nil] at hr
        subst hr
        cases e <;>
          (simp [bind, Except.bind, pure, Except.pure] at h; subst h; simp [byteStringToInteger_eq, hrepr])

/-- A big-endian byte sequence without a leading zero byte is `integerWidth` bytes long. -/
theorem integerWidth_repr256_be (d : List Char) (hd : ∀ c ∈ d, c.toNat < 256) (hmin : d.head? ≠ some '\x00') :
  integerWidth (repr256_be d) = d.length :=
    by
      cases d with
      | nil => rfl
      | cons c t =>
          have hc0 : c.toNat ≠ 0 := by
            intro h0; apply hmin; simp; rw [← Char.ofNat_toNat c, h0]
          have hlt := repr256_be_lt (c :: t) hd
          have hpos : 0 < 256 ^ t.length := Nat.pow_pos (by decide)
          rw [repr256_be_cons] at hlt ⊢
          have hle : 256 ^ t.length ≤ c.toNat * 256 ^ t.length + repr256_be t := by
            have := Nat.mul_le_mul_right (256 ^ t.length) (Nat.one_le_iff_ne_zero.mpr hc0)
            omega
          generalize c.toNat * 256 ^ t.length + repr256_be t = m at hlt hle
          have hne : m ≠ 0 := by omega
          rw [List.length_cons] at hlt ⊢
          rw [← pow2_pow256] at hlt hle
          have h1 := (Nat.le_log2 hne).mpr hle
          have h2 := (Nat.log2_lt hne).mpr hlt
          unfold integerWidth
          split
          · contradiction
          · omega

/-- `integerToByteString` rebuilds a bytestring from its integer value, provided the width it
    selects (`w`, or `integerWidth` of the value when `w = 0`) is the length of `s`. -/
theorem integerToByteString_bytes (e : Bool) (s : String) (w : Nat)
    (hbytes : ∀ c ∈ s.data, c.toNat < 256) (hlen : String.length s ≤ 8192)
    (hw : (if w = 0 then integerWidth (repr256_be (if e then s.data else s.data.reverse)) else w) = String.length s) :
  integerToByteString e w (byteStringToInteger e s) = .ok s :=
    by
      obtain ⟨l⟩ := s
      simp only [byteStringToInteger_eq, String.length_mk] at hbytes hlen hw ⊢
      have hd : ∀ c ∈ (if e then l else l.reverse), c.toNat < 256 := by
        cases e <;> simpa using hbytes
      have hdlen : (if e then l else l.reverse).length = l.length := by
        cases e <;> simp
      have hw8 : w ≤ 8192 := by
        by_cases hw0 : w = 0
        · omega
        · rw [if_neg hw0] at hw; omega
      have hlt : repr256_be (if e then l else l.reverse) < 2 ^ 65536 := by
        have h1 := repr256_be_lt _ hd
        rw [hdlen, ← pow2_pow256] at h1
        exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (n := 2) (j := 65536) (by decide) (by omega))
      rw [integerToByteString_nat e w _ hw8 (fun _ => hlt), hw, ← hdlen,
          itobs_be_loop_repr _ [] hd, List.append_nil]
      cases e <;> simp [bind, Except.bind, pure, Except.pure]

-- itobs_le (w, n) = itobs_be (w, n) = ×, if n < 0 or n ≥ 2 ^ 65536
/-- Given `w` and `n`, if n < 0 or n > 2 ^ 65536, `integerToByteString` returns an error. -/
theorem integerToByteString_n_bounds_err (e : Bool) (w n : Integer) : n < 0 ∨ n ≥ 2 ^ 65536 →
  (integerToByteString e w n |> Except.isError) :=
    by
      intro hn
      unfold Integer at *
      by_cases hw0 : w < 0
      · rw [integerToByteString_neg_w e w n hw0]; rfl
      by_cases hw8 : w > 8192
      · rw [integerToByteString_high_w e w n hw8]; rfl
      cases hn with
      | inl hn =>
          rw [integerToByteString_neg_n e w n (Int.not_lt.mp hw0) (Int.not_lt.mp hw8) hn]; rfl
      | inr hn =>
          by_cases hwz : w = 0
          · subst hwz; rw [integerToByteString_zero_w_high_n e n hn]; rfl
          · have hn0 : 0 ≤ n := Int.le_trans (Int.pow_nonneg (by decide)) hn
            obtain ⟨w', rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ w)
            obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hn0
            have hn : 2 ^ 65536 ≤ n' := (Int.two_pow_le_natCast 65536 n').mp hn
            have hw' : w' ≠ 0 := by omega
            have hw8' : w' ≤ 8192 := by omega
            have hn' : 256 ^ w' ≤ n' := by
              rw [← pow2_pow256]
              exact Nat.le_trans (Nat.pow_le_pow_right (n := 2) (j := 65536) (by decide) (by omega)) hn
            rw [integerToByteString_nat e w' n' hw8' (fun h => absurd h hw'), if_neg hw',
                itobs_be_loop_high_n w' n' [] hn']
            rfl

example : byteStringToInteger false "\x56\x34\x12\x00\x00" = 0x123456 := rfl
example : byteStringToInteger true  "\x00\x00\x12\x34\x56" = 0x123456 := rfl

/-- `byteStringToInteger` followed by `integerToByteString` at the input's own length is the
    identity on bytestrings (characters `< 256`) of at most 8192 bytes. -/
theorem bstoi_itobs_roundtrip (e : Bool) (s : String) (hbytes : ∀ c ∈ s.data, c.toNat < 256) (hlen : String.length s ≤ 8192) :
  integerToByteString e (String.length s) (byteStringToInteger e s) = .ok s :=
    by
      apply integerToByteString_bytes e s _ hbytes hlen
      split
      next h =>
        obtain ⟨l⟩ := s
        simp only [String.length_mk, List.length_eq_zero_iff] at h
        subst h
        cases e <;> rfl
      next => rfl

/-- A successful `integerToByteString` result reads back as `n`. -/
theorem itobs_bstoi_equivalence (e : Bool) (s : String) (w n : Integer) :
  integerToByteString e w n = .ok s → byteStringToInteger e s = n :=
    by
      intro h
      unfold Integer at *
      by_cases hw0 : w < 0
      · rw [integerToByteString_neg_w e w n hw0] at h; cases h
      by_cases hw8 : w > 8192
      · rw [integerToByteString_high_w e w n hw8] at h; cases h
      by_cases hn0 : n < 0
      · rw [integerToByteString_neg_n e w n (Int.not_lt.mp hw0) (Int.not_lt.mp hw8) hn0] at h
        cases h
      by_cases hz : w = 0 ∧ n ≥ 2 ^ 65536
      · obtain ⟨hw, hn⟩ := hz
        subst hw
        rw [integerToByteString_zero_w_high_n e n hn] at h; cases h
      obtain ⟨w', rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ w)
      obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
      have hwn : w' = 0 → n' < 2 ^ 65536 := by
        intro hw
        have hn : ¬ (2 : Int) ^ 65536 ≤ (n' : Int) := fun hn => hz ⟨by subst hw; rfl, hn⟩
        exact Nat.lt_of_not_le (mt (Int.two_pow_le_natCast 65536 n').mpr hn)
      rw [integerToByteString_nat e w' n' (by omega) hwn] at h
      exact itobs_post_ok e _ n' s h

/-- `integerToByteString` inverts `byteStringToInteger` on a bytestring `s` (characters `< 256`,
    at most 8192 bytes) either at width `String.length s`, or at width `0` when `s` has no
    leading zero byte (`integerToByteString` with `w = 0` returns the minimal representation). -/
theorem bstoi_itobs_equivalence (e : Bool) (s : String) (w n : Integer) (hbytes : ∀ c ∈ s.data, c.toNat < 256) (hlen : String.length s ≤ 8192) :
  (w = 0 ∧ (if e then s.data else s.data.reverse).head? ≠ some '\x00') ∨ String.length s = w →
  byteStringToInteger e s = n
  → integerToByteString e w n = .ok s :=
    by
      intro hw hn
      subst hn
      rcases hw with ⟨rfl, hmin⟩ | hw
      · apply integerToByteString_bytes e s 0 hbytes hlen
        rw [if_pos rfl, integerWidth_repr256_be _ _ hmin]
        · obtain ⟨l⟩ := s
          cases e <;> simp
        · obtain ⟨l⟩ := s
          cases e <;> simpa using hbytes
      · subst hw
        exact bstoi_itobs_roundtrip e s hbytes hlen

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

-- TODO: formalizations for replicateByte

end PlutusCore.Bitwise
