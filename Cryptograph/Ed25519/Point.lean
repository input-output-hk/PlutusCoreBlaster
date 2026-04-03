import Cryptograph.Ed25519.Field

namespace Cryptograph.Ed25519.Point

/-! ## Ed25519 Curve Points-/

open Cryptograph.Ed25519.Field

-- Edwards curve parameter d = -121665/121666 (mod p)
def d : Fp := Fp.div (Fp.ofInt (-121665)) (Fp.ofNat 121666)

-- Point on Ed25519 curve in extended coordinates
structure EdPoint where
  x : Fp
  y : Fp
  z : Fp
  t : Fp

namespace EdPoint

-- Identity/neutral element (point at infinity)
def zero : EdPoint := ⟨Fp.zero, Fp.one, Fp.one, Fp.zero⟩

-- Check if point is the identity
def isZero (p : EdPoint) : Bool :=
  p.x = 0 && p.y = p.z

-- Convert from affine coordinates (x, y)
def fromAffine (x y : Fp) : EdPoint :=
  ⟨x, y, Fp.one, Fp.mul x y⟩

-- Convert to affine coordinates (x, y)
def toAffine (p : EdPoint) : Fp × Fp :=
  let zinv := Fp.inv p.z
  (Fp.mul p.x zinv, Fp.mul p.y zinv)

-- Point addition in extended coordinates
-- Based on the "add-2008-hwcd" formulas from EFD
def add (p q : EdPoint) : EdPoint :=
  let a := Fp.mul (Fp.sub p.y p.x) (Fp.sub q.y q.x)
  let b := Fp.mul (Fp.add p.y p.x) (Fp.add q.y q.x)
  let c := Fp.mul (Fp.mul p.t q.t) (Fp.add d d)
  let d := Fp.mul (Fp.mul p.z q.z) (Fp.ofNat 2)
  let e := Fp.sub b a
  let f := Fp.sub d c
  let g := Fp.add d c
  let h := Fp.add b a
  ⟨Fp.mul e f, Fp.mul g h, Fp.mul f g, Fp.mul e h⟩

instance : Add EdPoint := ⟨add⟩

-- Point doubling (optimized version of add(p, p))
-- Based on the "dbl-2008-hwcd" formulas from EFD
def double (p : EdPoint) : EdPoint :=
  let a := Fp.square p.x
  let b := Fp.square p.y
  let c := Fp.mul (Fp.ofNat 2) (Fp.square p.z)
  let h := Fp.add a b
  let e := Fp.sub h (Fp.square (Fp.add p.x p.y))
  let g := Fp.sub a b
  let f := Fp.add c g
  ⟨Fp.mul e f, Fp.mul g h, Fp.mul f g, Fp.mul e h⟩

-- Scalar multiplication using double-and-add algorithm
-- More efficient than repeated addition
partial def scalarMul (n : Nat) (p : EdPoint) : EdPoint :=
  if n = 0 then zero
  else if n = 1 then p
  else
    let half := scalarMul (n / 2) p
    let doubled := double half
    if n % 2 = 0 then doubled else add doubled p

-- Scalar multiplication from bytes (little-endian)
def scalarMulBytes (scalar : List UInt8) (p : EdPoint) : EdPoint :=
  let n := scalar.foldl (fun acc b => acc * 256 + b.toNat) 0
  scalarMul n p

-- Negate a point
def neg (p : EdPoint) : EdPoint :=
  ⟨Fp.neg p.x, p.y, p.z, Fp.neg p.t⟩

instance : Neg EdPoint := ⟨neg⟩

-- Ed25519 base point (generator)
-- x = 15112221349535400772501151409588531511454012693041857206046113283949847762202
-- y = 46316835694926478169428394003475163141307993866256225615783033603165251855960
def basePoint : EdPoint :=
  let x := Fp.ofNat 15112221349535400772501151409588531511454012693041857206046113283949847762202
  let y := Fp.ofNat 46316835694926478169428394003475163141307993866256225615783033603165251855960
  fromAffine x y

-- Decompress a point from y-coordinate and sign bit
-- Ed25519 uses point compression: only y and sign of x are stored
def decompress (yBytes : List UInt8) : Option EdPoint :=
  if yBytes.length ≠ 32 then none
  else
    -- Extract sign bit from last byte
    let lastByte := yBytes[31]!
    let xSign := lastByte >>> 7

    -- Clear sign bit to get y coordinate
    let yBytes := yBytes.set 31 (lastByte &&& 0x7F)
    let y := Fp.fromBytesLE yBytes

    -- Recover x from y using curve equation: x^2 = (y^2 - 1) / (d*y^2 + 1)
    let yy := Fp.square y
    let num := Fp.sub yy Fp.one
    let den := Fp.add (Fp.mul d yy) Fp.one
    let xx := Fp.div num den

    -- Compute square root (if exists)
    let x := Fp.pow xx ((p + 3) / 8)

    -- Check if x^2 = xx
    let check := Fp.square x
    if check != xx then
      -- Try x * sqrt(-1) if x^2 ≠ xx
      -- For p ≡ 5 mod 8, sqrt(-1) = 2^((p-1)/4) mod p (NOT (-1)^((p-1)/4))
      let sqrt_m1 := Fp.pow (Fp.ofNat 2) ((p - 1) / 4)
      let x := Fp.mul x sqrt_m1
      let check := Fp.square x
      if check != xx then none
      else
        -- Adjust sign of x
        let x := if (x.val % 2 == xSign.toNat) then x else Fp.neg x
        some (fromAffine x y)
    else
      -- Adjust sign of x
      let x := if (x.val % 2 == xSign.toNat) then x else Fp.neg x
      some (fromAffine x y)

-- Compress a point to 32 bytes (y-coordinate + sign bit)
def compress (p : EdPoint) : List UInt8 :=
  let (x, y) := toAffine p
  let yBytes := Fp.toBytesLE y
  -- Set high bit of last byte to sign of x
  let lastByte := yBytes[31]!
  let xSign := if x.val % 2 = 0 then 0 else 0x80
  let yBytes := yBytes.set 31 (lastByte ||| xSign)
  yBytes

end EdPoint

end Cryptograph.Ed25519.Point
