
namespace Cryptograph.BLS12_381

namespace Internal

open Neg (neg)

/-- The field modulus of the BLS12-381 curve. -/
@[simp] def fieldPrime : Nat := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- `fieldPrime` can be represented with a minimum of 381 bits. -/
theorem fieldPrime_is_381_bits : 1 + Nat.log2 fieldPrime = 381 := by rfl

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

/-- Tower extension fields in t, u, v and w -/
structure Fq1 where
  t : Fin fieldPrime
  deriving Repr, DecidableEq

structure Fq2 where
  u1 : Fq1
  u0 : Fq1
  deriving Repr, DecidableEq

structure Fq6 where
  v2 : Fq2
  v1 : Fq2
  v0 : Fq2
  deriving Repr, DecidableEq

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

def Fq6.ofNat (n : Nat) : Fq6 := ⟨0, 0, Fq2.ofNat n⟩
instance (n : Nat) : OfNat Fq6 n where
  ofNat := Fq6.ofNat n

def Fq12.ofNat (n : Nat) : Fq12 := ⟨0, Fq6.ofNat n⟩
instance (n : Nat) : OfNat Fq12 n where
  ofNat := Fq12.ofNat n

class Field (α : Type) extends Add α, Sub α, Neg α, Mul α, Inv α, LE α where
  ofNat            : Nat → α
  mulByNonResidual : α → α

open Field (mulByNonResidual)

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

inductive Point (α : Type) where
  | affine   : α → α → Point α
  | infinity : Point α
  deriving Repr, DecidableEq

def g1 : Point Fq1 :=
  .affine 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
          0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

def g2 : Point Fq2 :=
  .affine { u1 := 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e
          , u0 := 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8 }
          { u1 := 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be
          , u0 := 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801 }

/-- Checks whether a given point is on the curve.
    BLS12-381 curve equations are `y^2 = x^3 + 4` and `y^2 = x^3 + 4(u+1)` -/
def isOnCurve {α} [Field α] [DecidableEq α] : Point α → Bool
  | .infinity     => false
  | .affine ax ay => (ay * ay) = (ax * ax * ax + mulByNonResidual (Field.ofNat 4))

theorem g1_on_curve : isOnCurve g1 = true := by rfl
theorem g2_on_curve : isOnCurve g2 = true := by rfl

def pointDouble {α} [Field α] : Point α → Point α
  | .infinity     => .infinity
  | .affine x₁ y₁ =>
      let slope := ((Field.ofNat 3) * x₁ * x₁) * ((Field.ofNat 2) * y₁)⁻¹
      let x₂    := slope * slope - x₁ - x₁
      let y₂    := slope * (x₁ - x₂) - y₁
      .affine x₂ y₂

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

def pointNegate {α} [Field α] : Point α → Point α
  | .infinity   => .infinity
  | .affine x y => .affine x (-y)

instance {α} [Field α] : Neg (Point α) where
  neg := pointNegate

partial def pointBinaryMul {α} [DecidableEq α] [Field α] (acc : Point α) : Nat → Point α → Point α
  | 0, _ => acc
  | n, b =>
      let double := pointDouble b
      if 2 ∣ n then pointBinaryMul acc              (n / 2) double
               else pointBinaryMul (pointAdd acc b) (n / 2) double

def pointMul {α} [DecidableEq α] [Field α] (scalar : Int) (p : Point α) : Point α :=
  match scalar with
  | .ofNat   n => pointBinaryMul .infinity n       p
  | .negSucc n => pointBinaryMul .infinity (n + 1) (-p)

instance {α} [DecidableEq α] [Field α] : HMul Nat (Point α) (Point α) where
  hMul n := pointMul (.ofNat n)

instance {α} [DecidableEq α] [Field α] : HMul Int (Point α) (Point α) where
  hMul := pointMul

def isInSubGroup {α} [Field α] [DecidableEq α] (p : Point α) : Bool :=
  pointMul groupOrder p = .infinity

def untwistRoot    : Fq6  := ⟨0, 1, 0⟩
def untwistXFactor : Fq12 := ⟨0, untwistRoot⟩⁻¹
def untwistYFactor : Fq12 := ⟨untwistRoot, 0⟩⁻¹

def untwist : Point Fq2 → Option (Fq12 × Fq12)
  | .affine x y => .some ((⟨0, ⟨0, 0, x⟩⟩ * untwistXFactor), (⟨0, ⟨0, 0, y⟩⟩ * untwistYFactor))
  | .infinity   => .none

def millerDouble (r : Point Fq2) : Point Fq1 → Option Fq12
  | .infinity     => .none
  | .affine px py => do
      let (x, y) ← untwist r
      let slope  := (3 * x * x) * (2 * y)⁻¹
      let v      := y - slope * x
      pure ((Fq12.ofNat (Fin.val py.t)) - ((Fq12.ofNat (Fin.val px.t)) * slope) - v)

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

def calculateMillerLoop (p : Point Fq1) (q : Point Fq2) : Option Fq12 :=
  millerLoop p q q 1 (List.tail! millerLoopIterBinary)

partial def binaryPowLoop {α} [Field α] (a acc : α) : Nat → α
  | 0 => acc
  | n =>
      if 2 ∣ n then binaryPowLoop (a * a) acc       (n       / 2)
               else binaryPowLoop (a * a) (a * acc) ((n - 1) / 2)

def binaryPow {α} [Field α] (a : α) : Nat → α := binaryPowLoop a (Field.ofNat 1)

def calculatePairing (p : Point Fq1) (q : Point Fq2) : Option Fq12 := do
  let r ← calculateMillerLoop p q
  pure (binaryPow r finalExponent)

def finalVerify (a b : Fq12) : Bool :=
  binaryPow (a * b⁻¹) finalExponent = Fq12.ofNat 1

inductive Residuals α where
  | zero : Residuals α
  | one  : α → Residuals α
  | two  : α → α → Residuals α
  deriving DecidableEq

instance {α} [Repr α] : Repr (Residuals α) where
  reprPrec
    | .zero     , _ => ".zero"
    | .one x    , _ => ".one " ++ (repr x)
    | .two x₁ x₂, _ => ".two " ++ (repr x₁) ++ " " ++ (repr x₂)

def Residuals.mkTwo {α} [LE α] [DecidableLE α] (x₁ x₂ : α) : Residuals α :=
  match decide (x₁ ≤ x₂), decide (x₂ ≤ x₁) with
  | true , _     => .two x₁ x₂
  | false, true  => .two x₂ x₁
  | false, false => .one x₁

/-- Exponent used in quadratic residue (`sqrtMod`) calculation.
    Valid exponent, since `fieldPrime` is of the form `4 * p + 3`. -/
def Fq1.sqrtModExponent : Nat := (fieldPrime + 1) / 4

def Fq1.sqrtMod (a : Fq1) : Residuals Fq1 :=
  let x := binaryPow a Fq1.sqrtModExponent
  match decide (a = 0), decide (x * x = a) with
  | true , _     => .one 0
  | false, true  => Residuals.mkTwo x (-x)
  | false, false => .zero

/-- Exponent used for quadratic residue testing  -/
def Fq2.quadraticTestExponent : Nat := (fieldPrime ^ 2 - 1) / 2

def Fq2.algoTSValS := 3
def Fq2.algoTSValQ := 2002410280966213176492968580539871577211890012416319082482798067123247093561419642925082009912774178746869298192521341316387985567463363242025025302629554476386626629283976594752050996187041457677317627959721862496428249186185671
def Fq2.algoTSValZ := Fq2.mk 1 1

#eval binaryPow Fq2.algoTSValZ Fq2.quadraticTestExponent

theorem algoTSValues_correct_dist    : Fq2.algoTSValQ * (2 ^ Fq2.algoTSValS) = fieldPrime ^ 2 - 1   := by native_decide
theorem algoTSValues_correct_maximal : ¬ (2 ∣ Fq2.algoTSValQ)                                       := by native_decide
theorem algoTSValues_correct_z_nonresidual : binaryPow Fq2.algoTSValZ Fq2.quadraticTestExponent ≠ 1 := by native_decide

def Fq2.algoTSZPowQ := binaryPow Fq2.algoTSValZ Fq2.algoTSValQ

partial def Fq2.algoTSFindI (t : Fq2) (i : Nat) : Nat :=
       if t = 1 then i
  else Fq2.algoTSFindI (binaryPow t 2) (i + 1)

partial def Fq2.algoTSLoop (m : Nat) (c t r : Fq2) : Fq2 :=
       if t = 0 then 0
  else if t = 1 then r
  else let i  := Fq2.algoTSFindI t 0
       let b  := binaryPow c (2 ^ (m - i - 1))
       let b₂ := binaryPow b 2
       Fq2.algoTSLoop i b₂ (t * b₂) (r * b)

-- Tonelli-Shanks!
def Fq2.sqrtMod (n : Fq2) : Residuals Fq2 :=
  if binaryPow n Fq2.quadraticTestExponent ≠ 1
    then .zero
    else let r := Fq2.algoTSLoop Fq2.algoTSValS Fq2.algoTSZPowQ (binaryPow n Fq2.algoTSValQ) ((binaryPow n ((Fq2.algoTSValQ - 1) / 2)))
         Residuals.mkTwo r (-r)

end Internal

end Cryptograph.BLS12_381
