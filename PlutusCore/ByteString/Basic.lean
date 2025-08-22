import PlutusCore.Integer

namespace PlutusCore.ByteString
open PlutusCore.Integer

/-! ## Formalisation for PlutusCore ByteString representation and builtin functions. -/

namespace PlutusCore.ByteStringInternal

structure ByteString where
  data : String

instance : Inhabited ByteString where
  default := { data := "" }

/-- Preserve the string representation when transforming to ByteString
    i.e., no utf8 encoding is applied.
-/
@[simp] def ByteString.stringToByteString (s : String) : ByteString := { data := s }

@[inline] def byteStringToString (bs : ByteString) : String := bs.data

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
  compare x y := compare x.data y.data

/-- BEq instance for ByteString -/
instance BEqByteString : BEq ByteString where
  beq x y := x.data == y.data

/-! DecidableEq instance for ByteString -/

@[simp] theorem EqByteString_equiv_EqArray (x y : ByteString) : x.data = y.data ↔ x = y := by
  apply Iff.intro <;> intro h
  . match x, y with
    | ByteString.mk v1, ByteString.mk v2 => simp; assumption
  . rw [h]

theorem BEqByteString_true_imp_eq (x y : ByteString) : x == y → x = y := by simp [BEq.beq]

theorem BEqByteString_false_imp_not_eq (x y : ByteString) : (x == y) = false → x ≠ y := by simp [BEq.beq]

def ByteString.decEq (x y : ByteString) : Decidable (Eq x y) :=
  match h:(x == y) with
  | true => isTrue (BEqByteString_true_imp_eq _ _ h)
  | false => isFalse (BEqByteString_false_imp_not_eq _ _ h)

instance : DecidableEq ByteString := ByteString.decEq


/- LawfulBEq instance for ByteString -/
instance LawfulBEqByteString : LawfulBEq ByteString where
  eq_of_beq {a b} := BEqByteString_true_imp_eq a b
  rfl {bs} := by simp [BEq.beq]

@[simp] theorem ByteString.beq_iff_eq (x y : ByteString) : x == y ↔ x = y := by
  apply Iff.intro
  . apply BEqByteString_true_imp_eq
  . intro h
    rw [h]
    apply LawfulBEqByteString.rfl

/-- LT instance for ByteString -/
instance LTByteString : LT ByteString where
  lt x y := x.data < y.data

/-- Decidable LT instance for ByteString -/
instance : (x y : ByteString) → Decidable (x < y) :=
 fun x y => inferInstanceAs (Decidable (x.data < y.data))

/-- LE instance for ByteString -/
instance LEByteString : LE ByteString where
  le x y := x.data ≤ y.data

/-- Decidable LE instance for ByteString -/
instance : (x y : ByteString) → Decidable (x ≤ y) :=
 fun x y => inferInstanceAs (Decidable (x.data ≤ y.data))


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
  | ByteString.mk v =>
       unfold LT.lt LTByteString
       apply List.lt_irrefl

@[simp] def ByteString.length (bs : ByteString) : Nat := bs.data.length

def ByteString.cons (u :  UInt8) (bs : ByteString) : ByteString :=
  {data := String.singleton (Char.ofUInt8 u) ++ bs.data }

/-! ## Builtin ByteString functions. -/

/-- Return an empty ByteString
    NOTE: that this function is not a builtin. It is here provided for convenience.
-/
@[simp] def emptyByteString : ByteString := { data := "" }

/-- Given two ByteStrings `[c₁, ... cₘ]` and `[d₁, ..., dₙ]`, return `[c₁, ... cₘ, d₁, ..., dₙ]` -/
def appendByteString (b1 : ByteString) (b2 : ByteString) : ByteString := {data := String.append b1.data b2.data}

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
  let subString := bs.data.toList.extract (Max.max s (0 : Integer)).toNat (Min.min (s + k).toNat bs.data.length)
  {data := String.mk subString }


/-- Given ByteString `[c₁, ..., cₙ]` return `n` as result; -/
def lengthOfByteString (bs : ByteString) : Integer := Int.ofNat bs.length

/-- Given ByteString `[c₁, ..., cₙ₋₁]` and index `j` perform the following:
     - When 0 ≤ j ≤ n - 1
         - return cⱼ
     - Otherwise
         - return ⊥
-/
def indexByteString (bs : ByteString) (j : Integer) : Except String Integer :=
  if j < 0 then throw s!"indexByteString: index out of bounds: {j}"
  else
    match bs.data.toList[j.toNat]? with
    | none => throw s!"indexByteString: index out of bounds: {j}"
    | some c => pure c.toNat


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

