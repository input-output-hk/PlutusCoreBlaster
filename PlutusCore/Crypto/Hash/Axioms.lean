import PlutusCore.ByteString
import PlutusCore.Crypto.Hash.Basic

namespace PlutusCore.Crypto.Hash.Axioms

namespace Internal

open PlutusCore.ByteString

/-! ## Axiomatisation for PlutusCore hash builtin functions. -/

variable (x y : ByteString)

/- Axiom set: Hash lengths -/

axiom sha2_256_length    : (sha2_256    x).length = 32
axiom sha3_256_length    : (sha3_256    x).length = 32
axiom blake2b_224_length : (blake2b_224 x).length = 28
axiom blake2b_256_length : (blake2b_256 x).length = 32
axiom keccak_256_length  : (keccak_256  x).length = 32
axiom ripemd_160_length  : (ripemd_160  x).length = 20

@[simp] theorem sha2_256_data_length    : (sha2_256    x).data.length = 32 := sha2_256_length x
@[simp] theorem sha3_256_data_length    : (sha3_256    x).data.length = 32 := sha3_256_length x
@[simp] theorem blake2b_224_data_length : (blake2b_224 x).data.length = 28 := blake2b_224_length x
@[simp] theorem blake2b_256_data_length : (blake2b_256 x).data.length = 32 := blake2b_256_length x
@[simp] theorem keccak_256_data_length  : (keccak_256  x).data.length = 32 := keccak_256_length x
@[simp] theorem ripemd_160_data_length  : (ripemd_160  x).data.length = 20 := ripemd_160_length x

theorem sha2_256_lengthOf    : lengthOfByteString (sha2_256    x) = 32 := by simp only [lengthOfByteString, sha2_256_length]; rfl
theorem sha3_256_lengthOf    : lengthOfByteString (sha3_256    x) = 32 := by simp only [lengthOfByteString, sha3_256_length]; rfl
theorem blake2b_224_lengthOf : lengthOfByteString (blake2b_224 x) = 28 := by simp only [lengthOfByteString, blake2b_224_length]; rfl
theorem blake2b_256_lengthOf : lengthOfByteString (blake2b_256 x) = 32 := by simp only [lengthOfByteString, blake2b_256_length]; rfl
theorem keccak_256_lengthOf  : lengthOfByteString (keccak_256  x) = 32 := by simp only [lengthOfByteString, keccak_256_length]; rfl
theorem ripemd_160_lengthOf  : lengthOfByteString (ripemd_160  x) = 20 := by simp only [lengthOfByteString, ripemd_160_length]; rfl

/- Separation by width. One general lemma, then the two instances worth naming; the remaining
   cross-pairs follow the same way and are not worth enumerating. Note there are only three
   width classes -- 20, 28 and 32 -- so this separates ripemd_160 from everything and
   blake2b_224 from everything, and says nothing within the 32-byte class. -/

theorem ne_of_length_ne {a b : ByteString} : a.length ≠ b.length → a ≠ b := by
  intro hn he
  rw [he] at hn
  contradiction

theorem ripemd_160_ne_sha2_256 : ripemd_160 x ≠ sha2_256 y := by
  apply ne_of_length_ne
  rw [ripemd_160_length, sha2_256_length]
  decide

theorem blake2b_224_ne_blake2b_256 : blake2b_224 x ≠ blake2b_256 y := by
  apply ne_of_length_ne
  rw [blake2b_224_length, blake2b_256_length]
  decide

/- A digest is never empty. -/

theorem sha2_256_ne_empty    : sha2_256    x ≠ emptyByteString := by apply ne_of_length_ne; rw [sha2_256_length   ]; simp
theorem sha3_256_ne_empty    : sha3_256    x ≠ emptyByteString := by apply ne_of_length_ne; rw [sha3_256_length   ]; simp
theorem blake2b_224_ne_empty : blake2b_224 x ≠ emptyByteString := by apply ne_of_length_ne; rw [blake2b_224_length]; simp
theorem blake2b_256_ne_empty : blake2b_256 x ≠ emptyByteString := by apply ne_of_length_ne; rw [blake2b_256_length]; simp
theorem keccak_256_ne_empty  : keccak_256  x ≠ emptyByteString := by apply ne_of_length_ne; rw [keccak_256_length ]; simp
theorem ripemd_160_ne_empty  : ripemd_160  x ≠ emptyByteString := by apply ne_of_length_ne; rw [ripemd_160_length ]; simp

/- No collision property. -/

axiom NoCollision : ByteString → ByteString → Prop

axiom sha2_256_collision_free    : NoCollision x y → sha2_256    x = sha2_256    y → x = y
axiom sha3_256_collision_free    : NoCollision x y → sha3_256    x = sha3_256    y → x = y
axiom blake2b_224_collision_free : NoCollision x y → blake2b_224 x = blake2b_224 y → x = y
axiom blake2b_256_collision_free : NoCollision x y → blake2b_256 x = blake2b_256 y → x = y
axiom keccak_256_collision_free  : NoCollision x y → keccak_256  x = keccak_256  y → x = y
axiom ripemd_160_collision_free  : NoCollision x y → ripemd_160  x = ripemd_160  y → x = y

/- The distinctness direction, which the guarded-disequality version took as an axiom, is a theorem under this polarity. -/

theorem no_collision_ne_of_ne (f : ByteString → ByteString) :
  (∀ (x y : ByteString), NoCollision x y → f x = f y → x = y) →
  NoCollision x y →
  x ≠ y
  ----------------------------------------------------------------
  → f x ≠ f y :=
    by
      intros coll_free hnc hne he
      have hxy : x = y := coll_free x y hnc he
      contradiction

theorem sha2_256_ne_of_ne    : NoCollision x y → x ≠ y → sha2_256    x ≠ sha2_256    y := no_collision_ne_of_ne x y _ sha2_256_collision_free
theorem sha3_256_ne_of_ne    : NoCollision x y → x ≠ y → sha3_256    x ≠ sha3_256    y := no_collision_ne_of_ne x y _ sha3_256_collision_free
theorem blake2b_224_ne_of_ne : NoCollision x y → x ≠ y → blake2b_224 x ≠ blake2b_224 y := no_collision_ne_of_ne x y _ blake2b_224_collision_free
theorem blake2b_256_ne_of_ne : NoCollision x y → x ≠ y → blake2b_256 x ≠ blake2b_256 y := no_collision_ne_of_ne x y _ blake2b_256_collision_free
theorem keccak_256_ne_of_ne  : NoCollision x y → x ≠ y → keccak_256  x ≠ keccak_256  y := no_collision_ne_of_ne x y _ keccak_256_collision_free
theorem ripemd_160_ne_of_ne  : NoCollision x y → x ≠ y → ripemd_160  x ≠ ripemd_160  y := no_collision_ne_of_ne x y _ ripemd_160_collision_free

/- Axiom bundles -/

/-- The six digest widths. -/
def LengthAlg : Prop :=
  (∀ (b : ByteString), (sha2_256    b).length = 32) ∧
  (∀ (b : ByteString), (sha3_256    b).length = 32) ∧
  (∀ (b : ByteString), (blake2b_224 b).length = 28) ∧
  (∀ (b : ByteString), (blake2b_256 b).length = 32) ∧
  (∀ (b : ByteString), (keccak_256  b).length = 32) ∧
  (∀ (b : ByteString), (ripemd_160  b).length = 20)

theorem lengthAlg : LengthAlg :=
  ⟨sha2_256_length, sha3_256_length, blake2b_224_length,
   blake2b_256_length, keccak_256_length, ripemd_160_length⟩

/-- Guarded collision resistance. -/
def CollisionAlg : Prop :=
  (∀ (a b : ByteString), NoCollision a b → sha2_256    a = sha2_256    b → a = b) ∧
  (∀ (a b : ByteString), NoCollision a b → sha3_256    a = sha3_256    b → a = b) ∧
  (∀ (a b : ByteString), NoCollision a b → blake2b_224 a = blake2b_224 b → a = b) ∧
  (∀ (a b : ByteString), NoCollision a b → blake2b_256 a = blake2b_256 b → a = b) ∧
  (∀ (a b : ByteString), NoCollision a b → keccak_256  a = keccak_256  b → a = b) ∧
  (∀ (a b : ByteString), NoCollision a b → ripemd_160  a = ripemd_160  b → a = b)

theorem collisionAlg : CollisionAlg :=
  ⟨sha2_256_collision_free, sha3_256_collision_free, blake2b_224_collision_free,
   blake2b_256_collision_free, keccak_256_collision_free, ripemd_160_collision_free⟩

/-- The whole axiom set. -/
def AllAlg : Prop := LengthAlg ∧ CollisionAlg

theorem allAlg : AllAlg := ⟨lengthAlg, collisionAlg⟩

end Internal

export Internal
  ( -- digest widths
    sha2_256_length
    sha3_256_length
    blake2b_224_length
    blake2b_256_length
    keccak_256_length
    ripemd_160_length
    -- the same six in the shape plain `simp` leaves behind
    sha2_256_data_length
    sha3_256_data_length
    blake2b_224_data_length
    blake2b_256_data_length
    keccak_256_data_length
    ripemd_160_data_length
    -- widths in `Integer`, as the builtin has them
    sha2_256_lengthOf
    sha3_256_lengthOf
    blake2b_224_lengthOf
    blake2b_256_lengthOf
    keccak_256_lengthOf
    ripemd_160_lengthOf
    -- separation by width class
    ne_of_length_ne
    ripemd_160_ne_sha2_256
    blake2b_224_ne_blake2b_256
    -- a digest is never empty
    sha2_256_ne_empty
    sha3_256_ne_empty
    blake2b_224_ne_empty
    blake2b_256_ne_empty
    keccak_256_ne_empty
    ripemd_160_ne_empty
    -- the domain of the collision axioms
    NoCollision
    -- guarded collision resistance
    sha2_256_collision_free
    sha3_256_collision_free
    blake2b_224_collision_free
    blake2b_256_collision_free
    keccak_256_collision_free
    ripemd_160_collision_free
    -- the distinctness direction, derived
    sha2_256_ne_of_ne
    sha3_256_ne_of_ne
    blake2b_224_ne_of_ne
    blake2b_256_ne_of_ne
    keccak_256_ne_of_ne
    ripemd_160_ne_of_ne
    -- the axioms as bundles, with their witnesses
    LengthAlg
    lengthAlg
    CollisionAlg
    collisionAlg
    AllAlg
    allAlg
  )

end PlutusCore.Crypto.Hash.Axioms
