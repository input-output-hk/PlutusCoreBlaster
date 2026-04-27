import Cryptograph.Secp256k1.Field

namespace Cryptograph.Secp256k1.Point

/-! ## secp256k1 Curve Points-/

open Cryptograph.Secp256k1.Field

-- Point on secp256k1 curve in Jacobian coordinates
inductive Secp256k1Point where
  | infinity : Secp256k1Point
  | point : (x : Fp) → (y : Fp) → (z : Fp) → Secp256k1Point
  deriving BEq

namespace Secp256k1Point

-- Identity/neutral element (point at infinity)
def zero : Secp256k1Point := infinity

-- Check if point is the identity
def isZero (p : Secp256k1Point) : Bool :=
  match p with
  | infinity    => true
  | point _ _ z => z == 0

-- Convert from affine coordinates (x, y)
def fromAffine (x y : Fp) : Secp256k1Point :=
  point x y Fp.one

-- Convert to affine coordinates (x, y)
def toAffine (p : Secp256k1Point) : Option (Fp × Fp) :=
  match p with
  | infinity => none
  | point x y z =>
      if z == 0 then none
      else
        let zinv  := z⁻¹
        let zinv2 := zinv ^ 2
        let zinv3 := zinv2 * zinv
        some (Fp.mul x zinv2, Fp.mul y zinv3)

-- Point doubling in Jacobian coordinates
-- Based on the "dbl-2007-bl" formulas for a=0
partial def double (p : Secp256k1Point) : Secp256k1Point :=
  match p with
  | infinity => infinity
  | point x y z =>
    if y == 0 then infinity
    else
      let xx   := x^2
      let yy   := y^2
      let yyyy := yy^2
      let zz   := z^2
      let s    := 2 * ((x + yy)^2 - xx - yyyy)
      let m    := 3 * xx
      let x3   := m^2 - 2 * s
      let y3   := m * (s - x3) - 8 * yyyy
      let z3 := (y + z)^2 - yy - zz
      point x3 y3 z3

-- Point addition in Jacobian coordinates
-- Based on the "add-2007-bl" formulas
partial def add (p q : Secp256k1Point) : Secp256k1Point :=
  match p, q with
  | infinity, _ => q
  | _, infinity => p
  | point x1 y1 z1, point x2 y2 z2 =>
      let z1z1 := z1^2
      let z2z2 := z2^2
      let u1   := x1 * z2z2
      let u2   := x2 * z1z1
      let s1   := y1 * z2 * z2z2
      let s2   := y2 * z1 * z1z1

      if u1 == u2 then
        if s1 == s2 then double p  -- Same point, use doubling
        else infinity  -- Inverse points
      else
        let h  := u2 - u1
        let i  := (2 * h) ^ 2
        let j  := h * i
        let r  := 2 * (s2 - s1)
        let v  := u1 * i
        let x3 := r^2 - j - 2 * v
        let y3 := r * (v - x3) - 2 * s1 * j
        let z3 := ((z1 + z2)^2 - z1z1 - z2z2) * h
        point x3 y3 z3

instance : Add Secp256k1Point := ⟨add⟩

-- Scalar multiplication using double-and-add algorithm
partial def scalarMul (n : Nat) (p : Secp256k1Point) : Secp256k1Point :=
  if n == 0 then zero
  else if n == 1 then p
  else
    let half := scalarMul (n / 2) p
    let doubled := double half
    if n % 2 == 0 then doubled else add doubled p

instance : HMul Nat Secp256k1Point Secp256k1Point := ⟨scalarMul⟩

-- Negate a point
def neg (p : Secp256k1Point) : Secp256k1Point :=
  match p with
  | infinity => infinity
  | point x y z => point x (Fp.neg y) z

instance : Neg Secp256k1Point := ⟨neg⟩

-- secp256k1 generator point (base point G)
-- G_x = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
-- G_y = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def basePoint : Secp256k1Point :=
  let gx := Fp.ofNat 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
  let gy := Fp.ofNat 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
  fromAffine gx gy

-- Checks if the point (`x`, `y`) is on the elliptic curve.
def isOnCurve (x y : Fp) : Bool := y^2 == x^3 + 7

-- Decompress a point from x-coordinate and sign bit (SEC1 encoding)
def decompress (bytes : List UInt8) : Option Secp256k1Point :=
  if h : bytes.length ≠ 33 then none
  else
    let prefixByte := bytes.head (by grind only [= List.length_nil])
    let xBytes     := bytes.tail
    let xOpt       := Fp.fromBytesBE xBytes
    match prefixByte == 0x02 || prefixByte == 0x03, xOpt with
    | true, some x =>
        let y2 := x ^ 3 + 7

        -- Compute square root using Tonelli-Shanks or direct formula
        -- For secp256k1, p ≡ 3 (mod 4), so y = yy^((p+1)/4)
        let y := Fp.pow y2 ((p + 1) / 4)

        -- Check if y² = yy
        if y ^ 2 != y2 then none
        else
          -- Adjust sign based on prefix byte
          let yIsEven := (y.val % 2 == 0)
          let shouldBeEven := (prefixByte == 0x02)
          let y := if yIsEven == shouldBeEven then y else Fp.neg y
          some (fromAffine x y)
    | _, _ => none

-- Compress a point to 33 bytes (prefix byte + x-coordinate)
def compress (p : Secp256k1Point) : Option (List UInt8) :=
  match toAffine p with
  | none => none
  | some (x, y) =>
    let prefixByte := if y.val % 2 = 0 then 0x02 else 0x03
    let xBytes := Fp.toBytesBE x
    some (prefixByte :: xBytes)

end Secp256k1Point

end Cryptograph.Secp256k1.Point
