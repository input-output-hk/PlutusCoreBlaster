import Cryptograph.BLS12_381.Basic

/-!
# Plutus-builtin-shaped surface for the pure BLS12-381 backend

The pure module in `Basic.lean` works with the concrete `Point Fq1`,
`Point Fq2`, and `Fq12` types and exposes `compressG1`, `pointAdd`,
etc. This file re-packages those operations under the same namespace
shape that the Plutus UPLC builtins (and the FFI mirror) use:
`G1.add`, `G1.scalarMul`, `Pairing.millerLoop`, ... — so call-sites can
swap pure ↔ FFI by changing one `import` / `open`.

Surface conventions, shared with `Cryptograph.FFI.BLS12_381.Surface`:

* Scalar-mul accepts a `List UInt8` (big-endian, ≤ 32 bytes); the pure
  side parses those bytes back into `Int`.
* `uncompress` and `hashToGroup` return `Option`.
* `millerLoop` is total. The pure side cannot prove totality from the
  type-level `Point` so it uses the multiplicative identity in `Fq12`
  as a fallback for the (unreachable in practice) `none` case.
-/

namespace Cryptograph.BLS12_381

open Internal (pointAdd pointNegate pointMul Field)

abbrev G1Point : Type := Point Fq1
abbrev G2Point : Type := Point Fq2
abbrev MlResult : Type := Fq12

private def scalarOfBytes (bs : List UInt8) : Int :=
  Int.ofNat (bs.foldl (fun acc b => acc * 256 + b.toNat) 0)

namespace G1

def add        : G1Point → G1Point → G1Point := pointAdd
def neg        : G1Point → G1Point := pointNegate
def scalarMul  (scalar : List UInt8) (p : G1Point) : G1Point := pointMul (scalarOfBytes scalar) p
def equal      (a b : G1Point) : Bool := decide (a = b)
def compress   : G1Point → List UInt8 := compressG1
def uncompress : List UInt8 → Option G1Point := uncompressG1
def hashToGroup (msg dst : List UInt8) : Option G1Point := Fq1.hashToCurve msg dst

end G1

namespace G2

def add        : G2Point → G2Point → G2Point := pointAdd
def neg        : G2Point → G2Point := pointNegate
def scalarMul  (scalar : List UInt8) (p : G2Point) : G2Point := pointMul (scalarOfBytes scalar) p
def equal      (a b : G2Point) : Bool := decide (a = b)
def compress   : G2Point → List UInt8 := compressG2
def uncompress : List UInt8 → Option G2Point := uncompressG2
def hashToGroup (msg dst : List UInt8) : Option G2Point := Fq2.hashToCurve msg dst

end G2

namespace Pairing

def millerLoop  (p : G1Point) (q : G2Point) : MlResult :=
  (calculateMillerLoop p q).getD (Field.ofNat 1)
def mulMlResult (a b : MlResult) : MlResult := a * b
def finalVerify : MlResult → MlResult → Bool := Cryptograph.BLS12_381.finalVerify

end Pairing

end Cryptograph.BLS12_381
