import Cryptograph.Integer
import Cryptograph.Sha2.Sha256

namespace Cryptograph.BLS12_381

namespace Internal

open Neg (neg)

open Cryptograph.Integer
open Cryptograph.Sha2

/-- The field modulus of the BLS12-381 curve. -/
@[simp] def fieldPrime : Nat := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- `fieldPrime` can be represented with a minimum of 381 bits. -/
theorem fieldPrime_is_381_bits : 1 + Nat.log2 fieldPrime = 381 := by rfl

/-- `fieldPrime` is smaller than 2 ^ 381. -/
theorem fieldPrime_representable_in_381_bits : fieldPrime < 2 ^ 381 := by decide +native

/-- The group order of the BLS12-381 curve. -/
def groupOrder : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- `groupOrder` can be represented with a minimum of 255 bits. -/
theorem groupOrder_is_255_bits : 1 + Nat.log2 groupOrder = 255 := by rfl

/-- The number of iterations the Miller loop must take.  -/
def millerLoopIter : BitVec 64 := 0xd201000000010000
/-- The binary representation of the number of iterations for the Miller loop. -/
def millerLoopIterBinary : List Bool := millerLoopIter.getMsbD <$> List.range 64

/-- The final exponent used in calculating the pairing.
    Note: this number is huge. -/
def finalExponent : Nat := (fieldPrime ^ 12 - 1) / groupOrder

/-- Field Fq1 -/
structure Fq1 where
  t : Fin fieldPrime
  deriving Repr, DecidableEq

/-- Field Fq2 -/
structure Fq2 where
  u1 : Fq1
  u0 : Fq1
  deriving Repr, DecidableEq

/-- Tower extension Fq6 -/
structure Fq6 where
  v2 : Fq2
  v1 : Fq2
  v0 : Fq2
  deriving Repr, DecidableEq

/-- Field Fq12 -/
structure Fq12 where
  w1 : Fq6
  w0 : Fq6
  deriving Repr, DecidableEq

def Fq1.ofNat (n : Nat) : Fq1 := ⟨n % fieldPrime, by simp; omega⟩

instance (n : Nat) : OfNat Fq1 n where
  ofNat := Fq1.ofNat n

instance : Inhabited Fq1 where
  default := 0

instance : LE Fq1 where
  le x y := x.t ≤ y.t

instance (a b : Fq1) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.t ≤ b.t))

def Fq2.ofNat (n : Nat) : Fq2 := ⟨0, Fq1.ofNat n⟩
instance (n : Nat) : OfNat Fq2 n where
  ofNat := Fq2.ofNat n

instance : Inhabited Fq2 where
  default := ⟨0, 0⟩

def Fq6.ofNat (n : Nat) : Fq6 := ⟨0, 0, Fq2.ofNat n⟩
instance (n : Nat) : OfNat Fq6 n where
  ofNat := Fq6.ofNat n

def Fq12.ofNat (n : Nat) : Fq12 := ⟨0, Fq6.ofNat n⟩
instance (n : Nat) : OfNat Fq12 n where
  ofNat := Fq12.ofNat n

/-- Field operations necessary for the curve calculations. -/
class Field (α : Type) extends Add α, Sub α, Neg α, Mul α, Inv α, LE α where
  ofNat            : Nat → α
  mulByNonResidual : α → α

open Field (mulByNonResidual)

/-- Calculating the multiplicative inverse of `a` over the cyclic
    `p` field. -/
partial def binaryInversion (a p : Nat) : Nat :=
  if a == 0
    then panic! "inv of 0"
    else loop a p 1 0

 where

  evenLoop (a b : Nat) : Nat × Nat :=
    if 2 ∣ a
      then evenLoop (a / 2) ((if 2 ∣ b then b else b + p) / 2)
      else (a, b)

  loop (u v x₁ x₂ : Nat) : Nat :=
         if u = 1 then x₁ % p
    else if v = 1 then x₂ % p
    else let (u', x₁') := evenLoop u x₁
         let (v', x₂') := evenLoop v x₂
         if u' ≥ v' then loop (u' - v') v' (if x₁' ≥ x₂' then x₁' - x₂' else x₁' + p - x₂') x₂'
                    else loop u' (v' - u') x₁' (if x₂' ≥ x₁' then x₂' - x₁' else x₂' + p - x₁')

instance : Field Fq1 where
  ofNat   := Fq1.ofNat
  add x y := Fq1.ofNat (x.t + y.t)
  sub x y := Fq1.ofNat ((Fin.val x.t) + fieldPrime - (Fin.val y.t))
  neg x   := Fq1.ofNat (fieldPrime - (Fin.val x.t))
  mul x y := Fq1.ofNat (x.t * y.t)
  inv x   := Fq1.ofNat (binaryInversion (Fin.val x.t) fieldPrime)
  le x y  := x.t ≤ y.t
  mulByNonResidual x := x

/-- Lexicographical ordering of Prod. -/
def leProd {α β} [LE α] [LE β] [DecidableLE α] [DecidableLE β] : (α × β) → (α × β) → Bool
  | (x₁, x₂), (y₁, y₂) =>
      match decide (x₁ ≤ y₁), decide (y₁ ≤ x₁) with
      | true, true  => x₂ ≤ y₂
      | true, false => true
      | _   , _     => false

instance {α β} [LE α] [LE β] [DecidableLE α] [DecidableLE β] : LE (α × β) where
  le x y := leProd x y

instance {α β} [LE α] [LE β] [DecidableLE α] [DecidableLE β] : (x y : α × β) → Decidable (x ≤ y) :=
  fun x y => inferInstanceAs (Decidable (leProd x y))

def Fq2.inv (x : Fq2) : Fq2 :=
  let f := (x.u1 * x.u1 + x.u0 * x.u0)⁻¹
  { u1 := -x.u1 * f, u0 := x.u0 * f }

instance : Field Fq2 where
  ofNat   := Fq2.ofNat
  add x y := ⟨x.u1 + y.u1, x.u0 + y.u0⟩
  sub x y := ⟨x.u1 - y.u1, x.u0 - y.u0⟩
  neg x   := ⟨neg x.u1, neg x.u0⟩
  mul x y := ⟨x.u1 * y.u0 + x.u0 * y.u1, x.u0 * y.u0 - x.u1 * y.u1⟩
  inv     := Fq2.inv
  le x y  := (x.u1, x.u0) ≤ (y.u1, y.u0)
  mulByNonResidual x := ⟨x.u1 + x.u0, x.u0 - x.u1⟩

instance : (x y : Fq2) → Decidable (x ≤ y) :=
  fun x y => inferInstanceAs (Decidable ((x.u1, x.u0) ≤ (y.u1, y.u0)))

def Fq6.mul (x y : Fq6) : Fq6 :=
  let t0 := x.v0 * y.v0
  let t1 := x.v0 * y.v1 + x.v1 * y.v0
  let t2 := x.v0 * y.v2 + x.v1 * y.v1 + x.v2 * y.v0
  let t3 := mulByNonResidual (x.v1 * y.v2 + x.v2 * y.v1)
  let t4 := mulByNonResidual (x.v2 * y.v2)
  ⟨t2, t1 + t4, t0 + t3⟩

def Fq6.inv (x : Fq6) : Fq6 :=
  let t0 := x.v0 * x.v0 + mulByNonResidual (x.v1 * x.v2)
  let t1 := mulByNonResidual (x.v2 * x.v2) - x.v0 * x.v1
  let t2 := x.v1 * x.v1 - x.v0 * x.v2
  let f  := (x.v0 * t0 + mulByNonResidual (x.v2 * t1) + mulByNonResidual (x.v1 * t2))⁻¹
  ⟨t2 * f, t1 * f, t0 * f⟩

instance : Field Fq6 where
  ofNat   := Fq6.ofNat
  add x y := ⟨x.v2 + y.v2, x.v1 + y.v1, x.v0 + y.v0⟩
  sub x y := ⟨x.v2 - y.v2, x.v1 - y.v1, x.v0 - y.v0⟩
  neg x   := ⟨neg x.v2   , neg x.v1   , neg x.v0   ⟩
  mul     := Fq6.mul
  inv     := Fq6.inv
  le x y  := (x.v2, x.v1, x.v0) ≤ (y.v2, y.v1, y.v0)
  mulByNonResidual x := ⟨x.v1, x.v0, mulByNonResidual x.v2⟩

instance : (x y : Fq6) → Decidable (x ≤ y) :=
  fun x y => inferInstanceAs (Decidable ((x.v2, x.v1, x.v0) ≤ (y.v2, y.v1, y.v0)))

instance : Inhabited Fq12 where
  default := Fq12.ofNat 0

def Fq12.inv (x : Fq12) : Fq12 :=
  let f := (x.w0 * x.w0 - mulByNonResidual (x.w1 * x.w1))⁻¹
  ⟨-x.w1 * f, x.w0 * f⟩

instance : Field Fq12 where
  ofNat   := Fq12.ofNat
  add x y := ⟨x.w1 + y.w1, x.w0 + y.w0⟩
  sub x y := ⟨x.w1 - y.w1, x.w0 - y.w0⟩
  neg x   := ⟨neg x.w1, neg x.w0⟩
  mul x y := ⟨x.w1 * y.w0 + x.w0 * y.w1, x.w0 * y.w0 + mulByNonResidual (x.w1 * y.w1)⟩
  inv     := Fq12.inv
  le x y  := (x.w1, x.w0) ≤ (y.w1, y.w0)
  mulByNonResidual x := ⟨mulByNonResidual x.w1, mulByNonResidual x.w0⟩

/-- Represents a point on the 2 dimensional space over `α`.
    Not all points are on the elliptic curve. -/
inductive Point (α : Type) where
  | affine   : α → α → Point α
  | infinity : Point α
  deriving Repr, DecidableEq

instance : Inhabited (Point α) where
  default := .infinity

/-- The canonical generator point of G1. -/
def g1 : Point Fq1 :=
  .affine 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
          0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

/-- The canonical generator point of G2. -/
def g2 : Point Fq2 :=
  .affine { u1 := 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e
          , u0 := 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8 }
          { u1 := 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be
          , u0 := 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801 }

/-- Checks whether a given point is on the curve.
    BLS12-381 curve equations are `y^2 = x^3 + 4` and `y^2 = x^3 + 4(u+1)`. -/
def isOnCurve {α} [Field α] [DecidableEq α] : Point α → Bool
  | .infinity     => false
  | .affine ax ay => (ay * ay) = (ax * ax * ax + mulByNonResidual (Field.ofNat 4))

theorem g1_on_curve : isOnCurve g1 = true := by rfl
theorem g2_on_curve : isOnCurve g2 = true := by rfl

/-- Calculates adding a point to itself on the elliptic curve. -/
def pointDouble {α} [Field α] : Point α → Point α
  | .infinity     => .infinity
  | .affine x₁ y₁ =>
      let slope := ((Field.ofNat 3) * x₁ * x₁) * ((Field.ofNat 2) * y₁)⁻¹
      let x₂    := slope * slope - x₁ - x₁
      let y₂    := slope * (x₁ - x₂) - y₁
      .affine x₂ y₂

/-- Calculates the addition of two points on the elliptic curve. -/
def pointAdd {α} [DecidableEq α] [Field α] : Point α → Point α → Point α
  | .infinity    , p             => p
  | p            , .infinity     => p
  | .affine x₁ y₁, .affine x₂ y₂ =>
           if x₁ = x₂ ∧ y₁ = y₂ then pointDouble (.affine x₁ y₁)
      else if x₁ = x₂ ∧ y₁ ≠ y₂ then .infinity
      else let slope := (y₂ - y₁) * (x₂ - x₁)⁻¹
           let x₃    := slope * slope - x₁ - x₂
           let y₃    := slope * (x₁ - x₃) - y₁
           .affine x₃ y₃

instance {α} [DecidableEq α] [Field α] : Add (Point α) where
  add := pointAdd

/-- Calculates the additive inverse of a point on the curve. -/
def pointNegate {α} [Field α] : Point α → Point α
  | .infinity   => .infinity
  | .affine x y => .affine x (-y)

instance {α} [Field α] : Neg (Point α) where
  neg := pointNegate

/-- Calculates adding a point to itself `n` times on the curve. -/
partial def pointBinaryMul {α} [DecidableEq α] [Field α] (acc : Point α) : Nat → Point α → Point α
  | 0, _ => acc
  | n, b =>
      let double := pointDouble b
      if 2 ∣ n then pointBinaryMul acc              (n / 2) double
               else pointBinaryMul (pointAdd acc b) (n / 2) double

/-- Calculates the multiplication of point `p` with a `scalar` on the curve. -/
def pointMul {α} [DecidableEq α] [Field α] (scalar : Int) (p : Point α) : Point α :=
  match scalar with
  | .ofNat   n => pointBinaryMul .infinity n       p
  | .negSucc n => pointBinaryMul .infinity (n + 1) (-p)

instance {α} [DecidableEq α] [Field α] : HMul Nat (Point α) (Point α) where
  hMul n := pointMul (.ofNat n)

instance {α} [DecidableEq α] [Field α] : HMul Int (Point α) (Point α) where
  hMul := pointMul

/-- Determines if point `p` is in the subgroup. -/
def isInSubGroup {α} [Field α] [DecidableEq α] (p : Point α) : Bool :=
  pointMul groupOrder p = .infinity

/-- Root factor used in the "sextic twist". -/
def untwistRoot    : Fq6  := ⟨0, 1, 0⟩
/-- Untwist factor for the `x` coordinate. -/
def untwistXFactor : Fq12 := ⟨0, untwistRoot⟩⁻¹
/-- Untwist factor for the `y` coordinate. -/
def untwistYFactor : Fq12 := ⟨untwistRoot, 0⟩⁻¹

/-- Untwists a point to the 12 dimensional Fq12 curve. -/
def untwist : Point Fq2 → Option (Fq12 × Fq12)
  | .affine x y => .some ((⟨0, ⟨0, 0, x⟩⟩ * untwistXFactor), (⟨0, ⟨0, 0, y⟩⟩ * untwistYFactor))
  | .infinity   => .none

/-- "Doubling" operation of the Miller loop. -/
def millerDouble (r : Point Fq2) : Point Fq1 → Option Fq12
  | .infinity     => .none
  | .affine px py => do
      let (x, y) ← untwist r
      let slope  := (3 * x * x) * (2 * y)⁻¹
      let v      := y - slope * x
      pure ((Fq12.ofNat (Fin.val py.t)) - ((Fq12.ofNat (Fin.val px.t)) * slope) - v)

/-- "Addition" operation of the Miller loop. -/
def millerAdd (r q : Point Fq2) : Point Fq1 → Option Fq12
  | .infinity     => .none
  | .affine px py => do
      let (rx, ry) ← untwist r
      let (qx, qy) ← untwist q
      if rx = qx ∧ ry = -qy
        then pure ((Fq12.ofNat (Fin.val px.t)) - rx)
        else let slope := (qy - ry) * (qx - rx)⁻¹
             let v     := ((qy * rx) - (ry * qx)) * (rx - qx)⁻¹
             pure ((Fq12.ofNat (Fin.val py.t)) - (Fq12.ofNat (Fin.val px.t) * slope) - v)

/-- The Miller loop is used to calculate the pairing of points `p` and `q`. -/
def millerLoop (p : Point Fq1) (q : Point Fq2) (r : Point Fq2) (acc : Fq12) : List Bool → Option Fq12
  | []        => pure acc
  | true :: t => do
      let dr := pointDouble r
      let md ← millerDouble r p
      let ma ← millerAdd dr q p
      millerLoop p q (pointAdd dr q) (acc * acc * md * ma) t
  | false :: t => do
      let dr := pointDouble r
      let md ← millerDouble r p
      millerLoop p q dr (acc * acc * md) t

/-- Calculates the value of the pairing (E) for point `p` and `q` without the final exponentiation.
    Implementation uses the canonical Miller loop. -/
def calculateMillerLoop (p : Point Fq1) (q : Point Fq2) : Option Fq12 :=
  millerLoop p q q 1 (List.tail! millerLoopIterBinary)

/-- Tail-recursive implementation of the binary power. -/
def binaryPowLoop {α} [Field α] (a acc : α) (n : Nat) : α :=
  match h : n with
  | 0     => acc
  | p + 1 =>
      if 2 ∣ n then binaryPowLoop (a * a) acc       (n       / 2)
               else binaryPowLoop (a * a) (a * acc) ((n - 1) / 2)
  termination_by n
  decreasing_by omega; omega

/-- Optimized way to calculate the power `a ^ n`. -/
def binaryPow {α} [Field α] (a : α) : Nat → α := binaryPowLoop a (Field.ofNat 1)

/-- Calculates the value of the pairing (E) for point `p` and `q` via Miller loop. -/
def calculatePairing (p : Point Fq1) (q : Point Fq2) : Option Fq12 := do
  let r ← calculateMillerLoop p q
  pure (binaryPow r finalExponent)

/-- Verifies that `(a / b) ^ ((q ^ 12 - 1) / r)` is equal to 1. -/
def finalVerify (a b : Fq12) : Bool :=
  binaryPow (a * b⁻¹) finalExponent = Fq12.ofNat 1

/-- Represents quadratic residue values (calculated by `sqrtMod`). -/
inductive Residues α where
  | zero : Residues α
  | one  : α → Residues α
  | two  : α → α → Residues α
  deriving DecidableEq

/-- Specialized constructor function that ensures that the residues `x₁` and `x₂` are ordered. -/
def Residues.mkTwo {α} [LE α] [DecidableLE α] (x₁ x₂ : α) : Residues α :=
  match decide (x₁ ≤ x₂), decide (x₂ ≤ x₁) with
  | true , _     => .two x₁ x₂
  | false, true  => .two x₂ x₁
  | false, false => .one x₁

/-- Exponent used in quadratic residue (`sqrtMod`) calculation.
    Valid exponent, since `fieldPrime` is of the form `4 * p + 3`. -/
def Fq1.sqrtModExponent : Nat := (fieldPrime + 1) / 4

/-- Calculates the quadratic residues of `a`.
    The calculation is done using a simplified analytical method, since `fieldPrime = 4 * i + 3`. -/
def Fq1.sqrtMod (a : Fq1) : Residues Fq1 :=
  let x := binaryPow a Fq1.sqrtModExponent
  match decide (a = 0), decide (x * x = a) with
  | true , _     => .one 0
  | false, true  => Residues.mkTwo x (-x)
  | false, false => .zero

/-- Determines if `n` is a square in Fq. -/
def Fq1.isSquare (n : Fq1) : Bool := Fq1.sqrtMod n ≠ .zero

/-- Exponent used for quadratic residue testing. -/
def Fq2.quadraticTestExponent : Nat := (fieldPrime ^ 2 - 1) / 2

/-- Determines if `n` is square in Fq2 using Euler's Criterion. -/
def Fq2.isSquare (n : Fq2) : Bool :=
  let e := binaryPow n Fq2.quadraticTestExponent
  e = 1 ∨ e = 0

/- Constants used by the Tonelli-Shanks algorithm. -/
def Fq2.algoTSValS  := 3
def Fq2.algoTSValQ  := 2002410280966213176492968580539871577211890012416319082482798067123247093561419642925082009912774178746869298192521341316387985567463363242025025302629554476386626629283976594752050996187041457677317627959721862496428249186185671
def Fq2.algoTSValZ  := Fq2.mk 1 1
def Fq2.algoTSZPowQ := binaryPow Fq2.algoTSValZ Fq2.algoTSValQ

theorem algoTSValues_correct_dist    : Fq2.algoTSValQ * (2 ^ Fq2.algoTSValS) = fieldPrime ^ 2 - 1   := by native_decide
theorem algoTSValues_correct_maximal : ¬ (2 ∣ Fq2.algoTSValQ)                                       := by native_decide
theorem algoTSValues_correct_z_nonresidual : binaryPow Fq2.algoTSValZ Fq2.quadraticTestExponent ≠ 1 := by native_decide

partial def Fq2.algoTSFindI (t : Fq2) (i : Nat) : Nat :=
       if t = 1 then i
  else Fq2.algoTSFindI (t * t) (i + 1)

partial def Fq2.algoTSLoop (m : Nat) (c t r : Fq2) : Fq2 :=
       if t = 0 then 0
  else if t = 1 then r
  else let i  := Fq2.algoTSFindI (t * t) 1
       let b  := binaryPow c (2 ^ (m - i - 1))
       let b₂ := b * b
       Fq2.algoTSLoop i b₂ (t * b₂) (r * b)

/-- Calculate the quadratic residue of `n` using the Tonelli-Shanks algorithm. -/
def Fq2.sqrtMod (n : Fq2) : Residues Fq2 :=
  if ¬ Fq2.isSquare n
    then .zero
    else let q := Fq2.algoTSValQ
         let m := Fq2.algoTSValS
         let c := Fq2.algoTSZPowQ
         let t := binaryPow n q
         let r := binaryPow n ((q + 1) / 2)
         let x := Fq2.algoTSLoop m c t r
         Residues.mkTwo x (-x)

/- "Hashing to Elliptic Curves" specification: (RFC9380) https://datatracker.ietf.org/doc/rfc9380/ -/

/- RFC9380: I2OSP functions -/
def i2osp₁ (n : Nat) : UInt8      := UInt8.ofNat n
def i2osp₂ (n : Nat) : List UInt8 := [ UInt8.ofNat (n >>> 8), UInt8.ofNat n ]

/- RFC9380: OS2IP function -/
def os2ip (x : List UInt8) : Nat :=
  let rec loop (acc : Nat) : List UInt8 → Nat
    | []     => acc
    | h :: t => loop (acc * 256 + (UInt8.toNat h)) t
  loop 0 x

/- RFC9380: strxor function -/
def strxor (a b : List UInt8) : List UInt8 :=
  let rec loop (acc : List UInt8) : List UInt8 → List UInt8 → List UInt8
    | h₁ :: t₁, h₂ :: t₂ => loop ((h₁ ^^^ h₂) :: acc) t₁ t₂
    | _       , _        => List.reverse acc
  loop [] a b

/- RFC9380: sgn0 function for G1 -/
def Fq1.sgn₀ (x : Fq1) : Fin 2 := ⟨x.t % 2, by omega⟩

/- Performs SHA256 hashing on the input message and produces the output as a byte list. -/
def sha256 (x : List UInt8) : List UInt8 :=
  List.flatMap UInt32.toUInt8BE (Vector.toList (Sha256.hashMessage x))

/-- Helper function to calculate running hashes of the message. -/
def expandMessageXmdLoop (acc : List (List UInt8)) (b₀ prev dst' : List UInt8) (ell i : Nat) : List UInt8 :=
  if i > ell
    then List.flatten (List.reverse acc)
    else let next := sha256 ((strxor b₀ prev) ++ [i2osp₁ i] ++ dst')
         expandMessageXmdLoop (next :: acc) b₀ next dst' ell (i + 1)
  termination_by (ell + 1 - i)
  decreasing_by omega

/-- Produces a uniformly random byte string using a cryptographic hash function SHA256.
    (RFC9380: expand_message_xmd). -/
def expandMessageXmd (msg dst : List UInt8) (l : Nat) : Option (List UInt8) :=
  let b   := 32
  let s   := 64
  let ell := Int.toNat (((l : Rat) / b).ceil)
  if ell > 255 ∨ l > 65535 ∨ (List.length dst) > 255
    then .none
    else
      let dst'   := dst ++ [i2osp₁ (List.length dst)]
      let zPad   := List.replicate s (0 : UInt8)
      let libStr := i2osp₂ l
      let msg'   := zPad ++ msg ++ libStr ++ [i2osp₁ 0] ++ dst'
      let b₀     := sha256 msg'
      let b₁     := sha256 (b₀ ++ [i2osp₁ 1] ++ dst')
      let uBytes := b₁ ++ expandMessageXmdLoop [] b₀ b₁ dst' ell 2
      .some (List.take l uBytes)

/-- Hashes arbitrary-length byte strings to a pair of Fq1 values.
    (RFC9380: hash_to_field) -/
def Fq1.hashToField (message dst : List UInt8) : Option (Fq1 × Fq1) := do
  let l      := 2 * 64
  let uBytes ← expandMessageXmd message dst l
  let u₀     := os2ip (List.take 64 uBytes)
  let u₁     := os2ip (List.drop 64 uBytes)
  (Fq1.ofNat u₀, Fq1.ofNat u₁)

/-- Maps a Fq1 value to the modified curve E'.
    (RFC9380: map_to_curve_simple_swu) -/
def Fq1.mapToCurveSimpleSWU (u : Fq1) : Fq1 × Fq1 :=
  let z      := Fq1.ofNat 11
  let a'     := Fq1.ofNat 0x00144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d
  let b'     := Fq1.ofNat 0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0
  let tv₁    := (z * z * u * u * u * u + z * u * u)⁻¹
  let x₁     := if tv₁ = 0
                  then b' * (z * a')⁻¹
                  else -b' * a'⁻¹ * (1 + tv₁)
  let gx₁    := x₁ * x₁ * x₁ + a' * x₁ + b'
  let x₂     := z * u * u * x₁
  let gx₂    := x₂ * x₂ * x₂ + a' * x₂ + b'
  let (x, y) :=
    match Fq1.sqrtMod gx₁ with
    | .one y   => (x₁, y)
    | .two y _ => (x₁, y)
    | .zero    =>
        match Fq1.sqrtMod gx₂ with
        | .one y   => (x₂, y)
        | .two y _ => (x₂, y)

        | .zero    => unreachable!
  let y' := if Fq1.sgn₀ u = Fq1.sgn₀ y then y else -y
  (x, y')

/-- Calculates all the (integer) powers of 'x' up to (and including) 'n' -/
def powersTo {α} [Field α] [OfNat α 1] (x : α) (n : Nat) : Vector α (n + 1) :=
  let rec loop (i : Nat) (acc : Vector α (i + 1)) (xp : α) (hi : i ≤ n) : Vector α (n + 1) :=
    if h : i = n
      then have acc' : Vector α (n + 1) := by rw [h] at acc; exact acc
           acc'
      else let xp' := x * xp
           loop (i + 1) (Vector.push acc xp') xp' (by omega)
  loop 0 #v[1] 1 (by simp)

/-- The 11-isogeny map from (x', y') on E' to (x, y) on E for Fq1.
    (RFC9380: 11-Isogeny Map for BLS12-381 G1). -/
def Fq1.isoMap (x y : Fq1) : Fq1 × Fq1 :=
  let xp   := powersTo x 15
  let xNum :=
      Fq1.ofNat 0x11a05f2b1e833340b809101dd99815856b303e88a2d7005ff2627b56cdb4e2c85610c2d5f2e62d6eaeac1662734649b7 * xp[ 0]
    + Fq1.ofNat 0x17294ed3e943ab2f0588bab22147a81c7c17e75b2f6a8417f565e33c70d1e86b4838f2a6f318c356e834eef1b3cb83bb * xp[ 1]
    + Fq1.ofNat 0x0d54005db97678ec1d1048c5d10a9a1bce032473295983e56878e501ec68e25c958c3e3d2a09729fe0179f9dac9edcb0 * xp[ 2]
    + Fq1.ofNat 0x1778e7166fcc6db74e0609d307e55412d7f5e4656a8dbf25f1b33289f1b330835336e25ce3107193c5b388641d9b6861 * xp[ 3]
    + Fq1.ofNat 0x0e99726a3199f4436642b4b3e4118e5499db995a1257fb3f086eeb65982fac18985a286f301e77c451154ce9ac8895d9 * xp[ 4]
    + Fq1.ofNat 0x1630c3250d7313ff01d1201bf7a74ab5db3cb17dd952799b9ed3ab9097e68f90a0870d2dcae73d19cd13c1c66f652983 * xp[ 5]
    + Fq1.ofNat 0x0d6ed6553fe44d296a3726c38ae652bfb11586264f0f8ce19008e218f9c86b2a8da25128c1052ecaddd7f225a139ed84 * xp[ 6]
    + Fq1.ofNat 0x17b81e7701abdbe2e8743884d1117e53356de5ab275b4db1a682c62ef0f2753339b7c8f8c8f475af9ccb5618e3f0c88e * xp[ 7]
    + Fq1.ofNat 0x080d3cf1f9a78fc47b90b33563be990dc43b756ce79f5574a2c596c928c5d1de4fa295f296b74e956d71986a8497e317 * xp[ 8]
    + Fq1.ofNat 0x169b1f8e1bcfa7c42e0c37515d138f22dd2ecb803a0c5c99676314baf4bb1b7fa3190b2edc0327797f241067be390c9e * xp[ 9]
    + Fq1.ofNat 0x10321da079ce07e272d8ec09d2565b0dfa7dccdde6787f96d50af36003b14866f69b771f8c285decca67df3f1605fb7b * xp[10]
    + Fq1.ofNat 0x06e08c248e260e70bd1e962381edee3d31d79d7e22c837bc23c0bf1bc24c6b68c24b1b80b64d391fa9c8ba2e8ba2d229 * xp[11]
  let xDen :=
      Fq1.ofNat 0x08ca8d548cff19ae18b2e62f4bd3fa6f01d5ef4ba35b48ba9c9588617fc8ac62b558d681be343df8993cf9fa40d21b1c * xp[ 0]
    + Fq1.ofNat 0x12561a5deb559c4348b4711298e536367041e8ca0cf0800c0126c2588c48bf5713daa8846cb026e9e5c8276ec82b3bff * xp[ 1]
    + Fq1.ofNat 0x0b2962fe57a3225e8137e629bff2991f6f89416f5a718cd1fca64e00b11aceacd6a3d0967c94fedcfcc239ba5cb83e19 * xp[ 2]
    + Fq1.ofNat 0x03425581a58ae2fec83aafef7c40eb545b08243f16b1655154cca8abc28d6fd04976d5243eecf5c4130de8938dc62cd8 * xp[ 3]
    + Fq1.ofNat 0x13a8e162022914a80a6f1d5f43e7a07dffdfc759a12062bb8d6b44e833b306da9bd29ba81f35781d539d395b3532a21e * xp[ 4]
    + Fq1.ofNat 0x0e7355f8e4e667b955390f7f0506c6e9395735e9ce9cad4d0a43bcef24b8982f7400d24bc4228f11c02df9a29f6304a5 * xp[ 5]
    + Fq1.ofNat 0x0772caacf16936190f3e0c63e0596721570f5799af53a1894e2e073062aede9cea73b3538f0de06cec2574496ee84a3a * xp[ 6]
    + Fq1.ofNat 0x14a7ac2a9d64a8b230b3f5b074cf01996e7f63c21bca68a81996e1cdf9822c580fa5b9489d11e2d311f7d99bbdcc5a5e * xp[ 7]
    + Fq1.ofNat 0x0a10ecf6ada54f825e920b3dafc7a3cce07f8d1d7161366b74100da67f39883503826692abba43704776ec3a79a1d641 * xp[ 8]
    + Fq1.ofNat 0x095fc13ab9e92ad4476d6e3eb3a56680f682b4ee96f7d03776df533978f31c1593174e4b4b7865002d6384d168ecdd0a * xp[ 9]
    +                                                                                                                xp[10]
  let yNum :=
      Fq1.ofNat 0x090d97c81ba24ee0259d1f094980dcfa11ad138e48a869522b52af6c956543d3cd0c7aee9b3ba3c2be9845719707bb33 * xp[ 0]
    + Fq1.ofNat 0x134996a104ee5811d51036d776fb46831223e96c254f383d0f906343eb67ad34d6c56711962fa8bfe097e75a2e41c696 * xp[ 1]
    + Fq1.ofNat 0x00cc786baa966e66f4a384c86a3b49942552e2d658a31ce2c344be4b91400da7d26d521628b00523b8dfe240c72de1f6 * xp[ 2]
    + Fq1.ofNat 0x01f86376e8981c217898751ad8746757d42aa7b90eeb791c09e4a3ec03251cf9de405aba9ec61deca6355c77b0e5f4cb * xp[ 3]
    + Fq1.ofNat 0x08cc03fdefe0ff135caf4fe2a21529c4195536fbe3ce50b879833fd221351adc2ee7f8dc099040a841b6daecf2e8fedb * xp[ 4]
    + Fq1.ofNat 0x16603fca40634b6a2211e11db8f0a6a074a7d0d4afadb7bd76505c3d3ad5544e203f6326c95a807299b23ab13633a5f0 * xp[ 5]
    + Fq1.ofNat 0x04ab0b9bcfac1bbcb2c977d027796b3ce75bb8ca2be184cb5231413c4d634f3747a87ac2460f415ec961f8855fe9d6f2 * xp[ 6]
    + Fq1.ofNat 0x0987c8d5333ab86fde9926bd2ca6c674170a05bfe3bdd81ffd038da6c26c842642f64550fedfe935a15e4ca31870fb29 * xp[ 7]
    + Fq1.ofNat 0x09fc4018bd96684be88c9e221e4da1bb8f3abd16679dc26c1e8b6e6a1f20cabe69d65201c78607a360370e577bdba587 * xp[ 8]
    + Fq1.ofNat 0x0e1bba7a1186bdb5223abde7ada14a23c42a0ca7915af6fe06985e7ed1e4d43b9b3f7055dd4eba6f2bafaaebca731c30 * xp[ 9]
    + Fq1.ofNat 0x19713e47937cd1be0dfd0b8f1d43fb93cd2fcbcb6caf493fd1183e416389e61031bf3a5cce3fbafce813711ad011c132 * xp[10]
    + Fq1.ofNat 0x18b46a908f36f6deb918c143fed2edcc523559b8aaf0c2462e6bfe7f911f643249d9cdf41b44d606ce07c8a4d0074d8e * xp[11]
    + Fq1.ofNat 0x0b182cac101b9399d155096004f53f447aa7b12a3426b08ec02710e807b4633f06c851c1919211f20d4c04f00b971ef8 * xp[12]
    + Fq1.ofNat 0x0245a394ad1eca9b72fc00ae7be315dc757b3b080d4c158013e6632d3c40659cc6cf90ad1c232a6442d9d3f5db980133 * xp[13]
    + Fq1.ofNat 0x05c129645e44cf1102a159f748c4a3fc5e673d81d7e86568d9ab0f5d396a7ce46ba1049b6579afb7866b1e715475224b * xp[14]
    + Fq1.ofNat 0x15e6be4e990f03ce4ea50b3b42df2eb5cb181d8f84965a3957add4fa95af01b2b665027efec01c7704b456be69c8b604 * xp[15]
  let yDen :=
      Fq1.ofNat 0x16112c4c3a9c98b252181140fad0eae9601a6de578980be6eec3232b5be72e7a07f3688ef60c206d01479253b03663c1 * xp[ 0]
    + Fq1.ofNat 0x1962d75c2381201e1a0cbd6c43c348b885c84ff731c4d59ca4a10356f453e01f78a4260763529e3532f6102c2e49a03d * xp[ 1]
    + Fq1.ofNat 0x058df3306640da276faaae7d6e8eb15778c4855551ae7f310c35a5dd279cd2eca6757cd636f96f891e2538b53dbf67f2 * xp[ 2]
    + Fq1.ofNat 0x16b7d288798e5395f20d23bf89edb4d1d115c5dbddbcd30e123da489e726af41727364f2c28297ada8d26d98445f5416 * xp[ 3]
    + Fq1.ofNat 0x0be0e079545f43e4b00cc912f8228ddcc6d19c9f0f69bbb0542eda0fc9dec916a20b15dc0fd2ededda39142311a5001d * xp[ 4]
    + Fq1.ofNat 0x08d9e5297186db2d9fb266eaac783182b70152c65550d881c5ecd87b6f0f5a6449f38db9dfa9cce202c6477faaf9b7ac * xp[ 5]
    + Fq1.ofNat 0x166007c08a99db2fc3ba8734ace9824b5eecfdfa8d0cf8ef5dd365bc400a0051d5fa9c01a58b1fb93d1a1399126a775c * xp[ 6]
    + Fq1.ofNat 0x16a3ef08be3ea7ea03bcddfabba6ff6ee5a4375efa1f4fd7feb34fd206357132b920f5b00801dee460ee415a15812ed9 * xp[ 7]
    + Fq1.ofNat 0x1866c8ed336c61231a1be54fd1d74cc4f9fb0ce4c6af5920abc5750c4bf39b4852cfe2f7bb9248836b233d9d55535d4a * xp[ 8]
    + Fq1.ofNat 0x167a55cda70a6e1cea820597d94a84903216f763e13d87bb5308592e7ea7d4fbc7385ea3d529b35e346ef48bb8913f55 * xp[ 9]
    + Fq1.ofNat 0x04d2f259eea405bd48f010a01ad2911d9c6dd039bb61a6290e591b36e636a5c871a5c29f4f83060400f8b49cba8f6aa8 * xp[10]
    + Fq1.ofNat 0x0accbb67481d033ff5852c1e48c50c477f94ff8aefce42d28c0f9a88cea7913516f968986f7ebbea9684b529e2561092 * xp[11]
    + Fq1.ofNat 0x0ad6b9514c767fe3c3613144b45f1496543346d98adf02267d5ceef9a00d9b8693000763e3b90ac11e99b138573345cc * xp[12]
    + Fq1.ofNat 0x02660400eb2e4f3b628bdd0d53cd76f2bf565b94e72927c1cb748df27942480e420517bd8714cc80d1fadc1326ed06f7 * xp[13]
    + Fq1.ofNat 0x0e0fa1d816ddc03e6b24255e0d7819c171c40f65e273b853324efcd6356caa205ca2f570f13497804415473a1d634b8f * xp[14]
    +                                                                                                                xp[15]
  (xNum * xDen⁻¹, y * yNum * yDen⁻¹)

/-- Calculates a point on the elliptic curve from an element of the finite field Fq1.
    (RFC9380: Simplified SWU for AB == 0) -/
def Fq1.mapToCurve (u : Fq1) : Point Fq1 :=
  let (x', y') := Fq1.mapToCurveSimpleSWU u
  let (x , y ) := Fq1.isoMap x' y'
  .affine x y

/-- Sends any point in Fq1 to the subgroup G1.
    (RFC9380: clear_cofactor) -/
def Fq1.clearCofactor (q : Point Fq1) : Point Fq1 :=
  let hEff := 0xd201000000010001
  hEff * q

/-- Uniform encoding from byte strings to points on the curve E₁.
    That is, the distribution of its output is statistically close to uniform in the subgroup.
    (RFC9380: hash_to_curve, BLS12381G1_XMD:SHA-256_SSWU_RO_) -/
def Fq1.hashToCurve (message dst : List UInt8) : Option (Point Fq1) := do
  let (u₀, u₁) ← Fq1.hashToField message dst
  let q₀       := Fq1.mapToCurve u₀
  let q₁       := Fq1.mapToCurve u₁
  let r        := q₀ + q₁
  let p        := Fq1.clearCofactor r
  p

/- RFC9380: sgn0 function for Fq2 -/
def Fq2.sgn₀ (x : Fq2) : Fin 2 :=
  let sign₀ := ¬ 2 ∣ (Fin.toNat x.u0.t)
  let zero₀ := x.u0 = 0
  let sign₁ := ¬ 2 ∣ (Fin.toNat x.u1.t)
  if sign₀ ∨ (zero₀ ∧ sign₁) then 1 else 0

/-- Creates an Fq2 value from 128 bytes. -/
def Fq2.ofBytes (x : List UInt8) : Fq2 :=
  let x₀ := os2ip (x |> List.take 64)
  let x₁ := os2ip (x |> List.drop 64 |> List.take 64)
  ⟨Fq1.ofNat x₁, Fq1.ofNat x₀⟩

/-- Hashes arbitrary-length byte strings to a pair of Fq2 values.
    (RFC9380: hash_to_field) -/
def Fq2.hashToField (message dst : List UInt8) : Option (Fq2 × Fq2) := do
  let l      := 2 * 2 * 64
  let uBytes ← expandMessageXmd message dst l
  let u₀     := Fq2.ofBytes uBytes
  let u₁     := Fq2.ofBytes (List.drop 128 uBytes)
  (u₀, u₁)

/-- Maps a G2 value to the modified curve E'.
    (RFC9380: map_to_curve_simple_swu) -/
def Fq2.mapToCurveSimpleSWU (u : Fq2) : Fq2 × Fq2 :=
  let z      := -⟨1, 2⟩
  let a'     := ⟨240, 0⟩
  let b'     := 1012 * ⟨1, 1⟩
  let tv₁    := (z * z * u * u * u * u + z * u * u)⁻¹
  let x₁     := if tv₁ = 0
                  then b' * (z * a')⁻¹
                  else -b' * a'⁻¹ * (1 + tv₁)
  let gx₁    := x₁ * x₁ * x₁ + a' * x₁ + b'
  let x₂     := z * u * u * x₁
  let gx₂    := x₂ * x₂ * x₂ + a' * x₂ + b'
  let (x, y) :=
    match Fq2.sqrtMod gx₁ with
    | .one y   => (x₁, y)
    | .two y _ => (x₁, y)
    | .zero    =>
        match Fq2.sqrtMod gx₂ with
        | .one y   => (x₂, y)
        | .two y _ => (x₂, y)
        | .zero    => unreachable!
  let y' := if Fq2.sgn₀ u = Fq2.sgn₀ y then y else -y
  (x, y')

/-- The 11-isogeny map from (x', y') on E' to (x, y) on E for Fq1.
    (RFC9380: 3-Isogeny Map for BLS12-381 G2). -/
def Fq2.isoMap (x y : Fq2) : Fq2 × Fq2 :=
  let xp   := powersTo x 3
  let I    := ⟨1, 0⟩
  let xNum :=
      (Fq2.ofNat 0x05c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6 + Fq2.ofNat 0x05c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6 * I) * xp[0]
    + (                                                                                                               Fq2.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a * I) * xp[1]
    + (Fq2.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e + Fq2.ofNat 0x08ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d * I) * xp[2]
    + (Fq2.ofNat 0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1                                                                                                                   ) * xp[3]
  let xDen :=
      (                                                                                                               Fq2.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63 * I) * xp[0]
    + (Fq2.ofNat 0xc                                                                                                + Fq2.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f * I) * xp[1]
    +                                                                                                                                                                                                                                     xp[2]
  let yNum :=
      (Fq2.ofNat 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706 + Fq2.ofNat 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706 * I) * xp[0]
    + (                                                                                                               Fq2.ofNat 0x05c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be * I) * xp[1]
    + (Fq2.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c + Fq2.ofNat 0x08ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f * I) * xp[2]
    + (Fq2.ofNat 0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10                                                                                                                   ) * xp[3]
  let yDen :=
      (Fq2.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb + Fq2.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb * I) * xp[0]
    + (                                                                                                               Fq2.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3 * I) * xp[1]
    + (Fq2.ofNat 0x12                                                                                               + Fq2.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99 * I) * xp[2]
    +                                                                                                                                                                                                                                     xp[3]
  (xNum * xDen⁻¹, y * yNum * yDen⁻¹)

/-- Calculates a point on the elliptic curve from an element of the finite field Fq2.
    (RFC9380: Simplified SWU for AB == 0) -/
def Fq2.mapToCurve (u : Fq2) : Point Fq2 :=
  let (x', y') := Fq2.mapToCurveSimpleSWU u
  let (x , y ) := Fq2.isoMap x' y'
  .affine x y

/-- Sends any point on the curve to the subgroup G2.
    (RFC9380: clear_cofactor) -/
def Fq2.clearCofactor (q : Point Fq2) : Point Fq2 :=
  let hEff := 0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551
  hEff * q

/-- Uniform encoding from byte strings to points in E₂.
    That is, the distribution of its output is statistically close to uniform in the subgroup.
    (RFC9380: hash_to_curve, BLS12381G2_XMD:SHA-256_SSWU_RO_) -/
def Fq2.hashToCurve (message dst : List UInt8) : Option (Point Fq2) := do
  let (u₀, u₁) ← Fq2.hashToField message dst
  let q₀       := Fq2.mapToCurve u₀
  let q₁       := Fq2.mapToCurve u₁
  let r        := q₀ + q₁
  let p        := Fq2.clearCofactor r
  p

def Fq1.ofBytesWithCheck (b : List UInt8) : Option Fq1 :=
  let n := os2ip b
  let x := Fq1.ofNat n
  if x.t.val = n
    then .some x
    else .none

def Fq1.findY (x : Fq1) (bigger : Bool) : Option Fq1 :=
  match Fq1.sqrtMod (binaryPow x 3 + 4) with
  | .zero      => .none
  | .one y     => .some y
  | .two y₁ y₂ => if bigger then y₂ else y₁

def Fq2.ofBytesWithCheck (b : List UInt8) : Option Fq2 :=
  let u₁' := os2ip (List.take 48 b)
  let u₀' := os2ip (List.drop 48 b)
  let u₁  := Fq1.ofNat u₁'
  let u₀  := Fq1.ofNat u₀'
  if u₁.t.val = u₁' ∧ u₀.t.val = u₀'
    then .some ⟨u₁, u₀⟩
    else .none

def Fq2.findY (x : Fq2) (bigger : Bool) : Option Fq2 :=
  match Fq2.sqrtMod (binaryPow x 3 + ⟨4, 4⟩) with
  | .zero      => .none
  | .one y     => .some y
  | .two y₁ y₂ => if bigger then y₂ else y₁

def compressG1 : Point Fq1 → List UInt8
  | .infinity   => 0b11000000 :: List.replicate 47 0
  | .affine x y =>
      let y' := Option.get! (Fq1.findY x false)
      let b  := UInt64.toUInt8BE (UInt64.ofNat x.t)
      let b0 := List.head b (by subst b; simp [UInt64.toUInt8BE, UInt32.toUInt8BE])
      let b' := List.tail b
      if y ≤ y'
        then (0b10000000 ||| b0) :: b'
        else (0b10100000 ||| b0) :: b'

def compressG2 : Point Fq2 → List UInt8
  | .infinity   => 0b11000000 :: List.replicate 95 0
  | .affine x y =>
      let y' := Option.get! (Fq2.findY x false)
      let b  := UInt64.toUInt8BE (UInt64.ofNat x.u1.t) ++ UInt64.toUInt8BE (UInt64.ofNat x.u0.t)
      let b0 := List.head b (by subst b; simp [UInt64.toUInt8BE, UInt32.toUInt8BE])
      let b' := List.tail b
      if y ≤ y'
        then (0b10000000 ||| b0) :: b'
        else (0b10100000 ||| b0) :: b'

def uncompress {α} [Field α] [DecidableEq α] (expectedLength : Nat) (he : expectedLength > 0) (ofBytes : List UInt8 → Option α) (findY : α → Bool → Option α) (b : List UInt8) : Option (Point α) :=
  if h : List.length b ≠ expectedLength
    then .none
    else let b0   := List.head b (by grind)
         let b₃₈₃ := decide (b0 &&& 0b10000000 > 0)
         let b₃₈₂ := decide (b0 &&& 0b01000000 > 0)
         let b₃₈₁ := decide (b0 &&& 0b00100000 > 0)
         let b0'  := b0 &&& 0b00011111
         let b'   := b0' :: List.tail b
         match b₃₈₃, b₃₈₂, b₃₈₁ with
         | true , true , false => if List.all b' (· = 0) then .some .infinity else .none
         | true , false, _     => do
             let x  ← ofBytes b'
             let y  ← findY x b₃₈₁
             let p  := .affine x y
             if isInSubGroup p
               then .some p
               else .none
         | _, _, _ => .none

def uncompressG1 : List UInt8 → Option (Point Fq1) := uncompress 48 (by simp) Fq1.ofBytesWithCheck Fq1.findY
def uncompressG2 : List UInt8 → Option (Point Fq2) := uncompress 96 (by simp) Fq2.ofBytesWithCheck Fq2.findY

end Internal

export Internal
  ( -- types
    Fq1
    Fq2
    Fq6
    Fq12
    Point
    Residues
    -- constants
    g1
    g2
    -- classes
    Field
    -- functions
    calculateMillerLoop
    calculatePairing
    finalVerify
    Fq1.hashToCurve
    Fq2.hashToCurve
    compressG1
    compressG2
    uncompressG1
    uncompressG2
  )

end Cryptograph.BLS12_381
