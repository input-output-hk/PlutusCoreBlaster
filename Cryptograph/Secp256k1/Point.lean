import Cryptograph.Secp256k1.Field

namespace Cryptograph.Secp256k1.Point

/-! ## secp256k1 Curve Points-/

open Cryptograph.Secp256k1.Field

-- Point on secp256k1 curve in Jacobian coordinates
inductive Secp256k1Point where
  | infinity : Secp256k1Point
  | point : (x : Fp) → (y : Fp) → (z : Fp) → Secp256k1Point

namespace Secp256k1Point

-- Identity/neutral element (point at infinity)
def zero : Secp256k1Point := infinity

-- Check if point is the identity
def isZero (p : Secp256k1Point) : Bool :=
  match p with
  | infinity => true
  | point _ _ z => z = 0

-- Convert from affine coordinates (x, y)
def fromAffine (x y : Fp) : Secp256k1Point :=
  point x y Fp.one

-- Convert to affine coordinates (x, y)
def toAffine (p : Secp256k1Point) : Option (Fp × Fp) :=
  match p with
  | infinity => none
  | point x y z =>
    if z = 0 then none
    else
      let zinv := Fp.inv z
      let zinv2 := Fp.square zinv
      let zinv3 := Fp.mul zinv2 zinv
      some (Fp.mul x zinv2, Fp.mul y zinv3)

-- Point doubling in Jacobian coordinates
-- Based on the "dbl-2007-bl" formulas for a=0
partial def double (p : Secp256k1Point) : Secp256k1Point :=
  match p with
  | infinity => infinity
  | point x y z =>
    if y = 0 then infinity
    else
      let xx := Fp.square x
      let yy := Fp.square y
      let yyyy := Fp.square yy
      let zz := Fp.square z
      let s := Fp.mul (Fp.ofNat 2) (Fp.square (Fp.sub (Fp.add x yy) xx))
      let m := Fp.add (Fp.mul (Fp.ofNat 3) xx) (Fp.mul (Fp.square (Fp.square z)) (Fp.ofNat 0))  -- a=0 for secp256k1
      let x3 := Fp.sub (Fp.square m) (Fp.add s s)
      let y3 := Fp.sub (Fp.mul m (Fp.sub s x3)) (Fp.mul (Fp.ofNat 8) yyyy)
      let z3 := Fp.mul (Fp.mul (Fp.add y z) (Fp.add y z)) (Fp.sub (Fp.square (Fp.add y z)) (Fp.add yy zz))
      point x3 y3 z3

-- Point addition in Jacobian coordinates
-- Based on the "add-2007-bl" formulas
partial def add (p q : Secp256k1Point) : Secp256k1Point :=
  match p, q with
  | infinity, _ => q
  | _, infinity => p
  | point x1 y1 z1, point x2 y2 z2 =>
    -- Check if same point
    if x1 = x2 && y1 = y2 && z1 = z2 then
      double p
    else
      let z1z1 := Fp.square z1
      let z2z2 := Fp.square z2
      let u1 := Fp.mul x1 z2z2
      let u2 := Fp.mul x2 z1z1
      let s1 := Fp.mul (Fp.mul y1 z2) z2z2
      let s2 := Fp.mul (Fp.mul y2 z1) z1z1

      if u1 = u2 then
        if s1 = s2 then double p  -- Same point, use doubling
        else infinity  -- Inverse points
      else
        let h := Fp.sub u2 u1
        let i := Fp.square (Fp.add h h)
        let j := Fp.mul h i
        let r := Fp.add (Fp.sub s2 s1) (Fp.sub s2 s1)
        let v := Fp.mul u1 i
        let x3 := Fp.sub (Fp.sub (Fp.square r) j) (Fp.add v v)
        let y3 := Fp.sub (Fp.mul r (Fp.sub v x3)) (Fp.add (Fp.mul s1 j) (Fp.mul s1 j))
        let z3 := Fp.mul (Fp.mul (Fp.add (Fp.add z1 z2) (Fp.add z1 z2)) (Fp.sub (Fp.square (Fp.add z1 z2)) (Fp.add z1z1 z2z2))) h
        point x3 y3 z3

instance : Add Secp256k1Point := ⟨add⟩

-- Scalar multiplication using double-and-add algorithm
partial def scalarMul (n : Nat) (p : Secp256k1Point) : Secp256k1Point :=
  if n = 0 then zero
  else if n = 1 then p
  else
    let half := scalarMul (n / 2) p
    let doubled := double half
    if n % 2 = 0 then doubled else add doubled p

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

-- Decompress a point from x-coordinate and sign bit (SEC1 encoding)
def decompress (bytes : List UInt8) : Option Secp256k1Point :=
  if bytes.length ≠ 33 then none
  else
    let prefixByte := bytes[0]!
    if prefixByte ≠ 0x02 && prefixByte ≠ 0x03 then none
    else
      let xBytes := bytes.tail
      let x := Fp.fromBytesBE xBytes

      -- Compute y² = x³ + 7
      let x3 := Fp.mul (Fp.square x) x
      let yy := Fp.add x3 (Fp.ofNat 7)

      -- Compute square root using Tonelli-Shanks or direct formula
      -- For secp256k1, p ≡ 3 (mod 4), so y = yy^((p+1)/4)
      let y := Fp.pow yy ((p + 1) / 4)

      -- Check if y² = yy
      if Fp.square y ≠ yy then none
      else
        -- Adjust sign based on prefix byte
        let yIsEven := (y % 2 = 0)
        let shouldBeEven := (prefixByte = 0x02)
        let y := if yIsEven = shouldBeEven then y else Fp.neg y
        some (fromAffine x y)

-- Compress a point to 33 bytes (prefix byte + x-coordinate)
def compress (p : Secp256k1Point) : Option (List UInt8) :=
  match toAffine p with
  | none => none
  | some (x, y) =>
    let prefixByte := if y % 2 = 0 then 0x02 else 0x03
    let xBytes := Fp.toBytesBE x
    some (prefixByte :: xBytes)

end Secp256k1Point

end Cryptograph.Secp256k1.Point
