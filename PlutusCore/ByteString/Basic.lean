import PlutusCore.Integer

namespace PlutusCore.ByteString
open PlutusCore.Integer

/-! ## Formalisation for PlutusCore ByteString representation and builtin functions. -/

namespace PlutusCore.ByteStringInternal

abbrev ByteString := ByteArray

/-- Base16-encode of ByteString to show result.
    Note that "<invalid byte>" is returned for invalid byte representation.
    Same behaviour as in PlutusTx.
-/
def ByteString.toHex (bs : ByteString) : String :=
  Array.foldr (fun u acc => (showWord8 u.toNat) ++ acc) "" bs.data

  where
    toHex (n : Nat) : String :=
      if n = 0 then "0" else
      if n = 1 then "1" else
      if n = 2 then "2" else
      if n = 3 then "3" else
      if n = 4 then "4" else
      if n = 5 then "5" else
      if n = 6 then "6" else
      if n = 7 then "7" else
      if n = 8 then "8" else
      if n = 9 then "9" else
      if n = 0xa then "a" else
      if n = 0xb then "b" else
      if n = 0xc then "c" else
      if n = 0xd then "d" else
      if n = 0xe then "e" else
      if n = 0xf then "f" else
      "<invalid byte>"

    showWord8 (n : Nat) : String :=
      s!"{toHex (n / 16)}{toHex (n % 16)}"

/-- Preserve the string representation when transforming to ByteString
    i.e., no utf8 encoding is applied.
-/
def ByteString.stringToByteString (s : String) : ByteString :=
  let rec loop
    | [],    r => r
    | c :: cs, r => loop cs (r.push c.toNat.toUInt8)
  ByteArray.mk  (loop s.data #[])

@[inline] def byteStringToString (bs : ByteString) : String :=
  let chars := Array.foldr (fun u acc => (Char.ofNat u.toNat) :: acc) [] bs.data
  String.mk chars

/-- ToString instance for ByteString -/
instance : ToString ByteString where
  toString bs := byteStringToString bs

/-- Repr instance for ByteString -/
instance : Repr ByteString where
  reprPrec x _ := byteStringToString x

/-- String to ByteString coercion to mimick OverloadedString in Haskell -/
instance : Coe String ByteString where
  coe s := ByteString.stringToByteString s
  -- NOTE: We are NOT using utf8 encoding here
  -- to replicate the Haskell semantics

/-- Ord instance for ByteString -/
instance OrdByteString : Ord ByteString where
  compare x y := Ord.arrayOrd.compare x.data y.data

/-- BEq instance for ByteString -/
instance BEqByteString : BEq ByteString where
  beq x y := x.data == y.data

/-! DecidableEq instance for ByteString -/

@[simp] theorem EqByteString_equiv_EqArray (x y : ByteString) : x.data = y.data ↔ x = y := by
  apply Iff.intro <;> intro h
  . match x, y with
    | ByteArray.mk v1, ByteArray.mk v2 => simp; assumption
  . rw [h]

theorem BEqByteString_true_imp_eq (x y : ByteString) : x == y → x = y := by
  simp [BEq.beq]
  intro h1
  apply (EqByteString_equiv_EqArray x y).1
  apply Array.eq_of_isEqv x.data y.data h1


theorem BEqByteString_false_imp_not_eq (x y : ByteString) : (x == y) = false → x ≠ y := by
  simp [BEq.beq]
  . match x, y with
    | ByteArray.mk v1, ByteArray.mk v2 =>
         simp; intro h1
         unfold Not
         intro h2
         have h3 : Array.isEqv v1 v2 (fun a b => a = b) := by
           rw [h2]
           apply Array.isEqv_self
         rw [Bool.eq_false_iff] at h1
         contradiction

def ByteString.decEq (x y : ByteString) : Decidable (Eq x y) :=
  match h:(x == y) with
  | true => isTrue (BEqByteString_true_imp_eq _ _ h)
  | false => isFalse (BEqByteString_false_imp_not_eq _ _ h)

instance : DecidableEq ByteString := ByteString.decEq


/- LawfulBEq instance for ByteString -/
instance LawfulBEqByteString : LawfulBEq ByteString where
  eq_of_beq {a b} := BEqByteString_true_imp_eq a b
  rfl {bs} := by simp [BEq.beq]; apply Array.isEqv_self


@[simp] theorem ByteString.beq_iff_eq (x y : ByteString) : x == y ↔ x = y := by
  apply Iff.intro
  . apply BEqByteString_true_imp_eq
  . intro h
    rw [h]
    apply LawfulBEqByteString.rfl

/-- LT instance for ByteString -/
instance LTByteString : LT ByteString where
  lt x y := x.data.toList < y.data.toList

/-- Decidable LT instance for ByteString -/
instance : (x y : ByteString) → Decidable (x < y) :=
 fun x y => inferInstanceAs (Decidable (x.data.toList < y.data.toList))

/-- LE instance for ByteString -/
instance LEByteString : LE ByteString where
  le x y := x.data.toList ≤ y.data.toList

/-- Decidable LE instance for ByteString -/
instance : (x y : ByteString) → Decidable (x ≤ y) :=
 fun x y => inferInstanceAs (Decidable (x.data.toList ≤ y.data.toList))



/-- NOTE: instance and theorem to be removed once added in Lean (currently not present) --/

theorem UInt8.lt_irrefl (x : UInt8) : ¬ x < x := by
  simp [LT.lt]
  unfold UInt8.lt
  simp only [LT.lt]
  apply Nat.lt_irrefl

instance : Std.Irrefl ( . < . : UInt8 → UInt8 → Prop) where
  irrefl := UInt8.lt_irrefl

@[simp] theorem ByteString.lt_irrefl (x : ByteString) : ¬ x < x := by
  match x with
  | ByteArray.mk v =>
       unfold LT.lt LTByteString
       apply List.lt_irrefl

def ByteString.cons (u :  UInt8) (bs : ByteString) : ByteString :=
  {data := #[u] ++ bs.data}

/-! ## Builtin ByteString functions. -/

/-- Return an empty ByteString
    NOTE: that this function is not a builtin. It is here provided for convenience.
-/
def emptyByteString : ByteString := ByteArray.empty

/-- Given two ByteStrings `[c₁, ... cₘ]` and `[d₁, ..., dₙ]`, return `[c₁, ... cₘ, d₁, ..., dₙ]` -/
def appendByteString (b1 : ByteString) (b2 : ByteString) : ByteString := b1 ++ b2

/-- Given integer `n` and ByteString `[c₁, ... cₘ]` return `[modInteger n 256, c₁, ... cₘ]` -/
def consByteStringV1 (n : Integer) (bs : ByteString) : ByteString :=
  match (modInteger n 256) with
  | Except.ok m => ByteString.cons m.toNat.toUInt8 bs
  | Except.error _ => unreachable!

/-- Given integer `n` and ByteString `[c₁, ... cₘ]` perform the following:
     - When 0 ≤ n ≤ 255:
         - return `[n, c₁, ... cₘ]`
     - Otherwise
         - return ⊥
-/
def consByteStringV2 (n : Integer) (bs : ByteString) : Except String ByteString :=
  if 0 <= n && n <= 255
  then pure (ByteString.cons n.toNat.toUInt8 bs)
  else throw "consByteStringV2: invalid byte representation"

/-- Given `s`, `k` and ByteString `[c₀, ..., cₙ]` return `[cₘₐₓ₍ₛ,₀₎, ..., cₘᵢₙ₍ₛ₊ₖ₋₁, ₙ₎]` -/
def sliceByteString (s : Integer) (k : Integer) (bs : ByteString) : ByteString :=
  -- Note that extract determine the number of elements by subtracting `s` and `k`.
  -- Hence, there is no need for us to subtract by one.
  bs.extract (Max.max s (0 : Integer)).toNat (Min.min (s + k).toNat bs.size)

/-- Given ByteString `[c₁, ..., cₙ]` return `n` as result; -/
def lengthOfByteString (bs : ByteString) : Integer := Int.ofNat bs.size

/-- Given ByteString `[c₁, ..., cₙ₋₁]` and index `j` perform the following:
     - When 0 ≤ j ≤ n - 1
         - return cⱼ
     - Otherwise
         - return ⊥
-/
def indexByteString (bs : ByteString) (j : Integer) : Except String Integer :=
  if 0 <= j && j <= bs.size - 1
  then pure (Int.ofNat bs[j.toNat]!.toNat)
  else throw s!"indexByteString: index out of bounds: {j}"

def equalsByteString (b1 : ByteString) (b2 : ByteString) : Bool := BEqByteString.beq b1 b2
def lessThanByteString (b1 : ByteString) (b2 : ByteString) : Bool := b1 < b2
def lessThanEqualsByteString (b1 : ByteString) (b2 : ByteString) : Bool := b1 <= b2

end PlutusCore.ByteStringInternal

export PlutusCore.ByteStringInternal
  ( -- type
    ByteString
    -- builtin functions
    appendByteString
    consByteStringV1
    consByteStringV2
    emptyByteString
    equalsByteString
    indexByteString
    lengthOfByteString
    lessThanByteString
    lessThanEqualsByteString
    sliceByteString
    ByteString.cons
    ByteString.stringToByteString
    -- theorems
    EqByteString_equiv_EqArray
    BEqByteString_false_imp_not_eq
    BEqByteString_true_imp_eq
    UInt8.lt_irrefl
    ByteString.beq_iff_eq
    ByteString.lt_irrefl
  )

end PlutusCore.ByteString

