import Cryptograph.BLS12_381
import PlutusCore.Crypto.BLS12_381.G1
import Blaster

/-! Symbolic BLS12-381 values.

While `Fq1.t` was a `Fin fieldPrime`, no goal with a symbolic `Fq1` could be translated:
Blaster rejects `Fin`, an inductive indexed by a term ("Inductive datatype with instance
parameters not supported: `Fin`"), and every `Fq2`, `Fq6`, `Fq12` and `Point` value carries
an `Fq1`. With `t : Nat`, the goals below translate. -/

namespace Cryptograph.BLS12_381.SymbolicPoints
open Cryptograph.BLS12_381.Internal
open PlutusCore.Crypto.BLS12_381.G1

/-- An `Fq1` is determined by its representative. -/
theorem fq1_eq_of_t_eq : ∀ (x y : Fq1), x.t = y.t → x = y := by blaster

/-- An affine point is never the point at infinity. -/
theorem affine_ne_infinity : ∀ (x y : Fq1), (Point.affine x y : Point Fq1) ≠ .infinity := by blaster

-- `bls12_381_G1_equal` is opaque, so it isn't known to hold of any two points.
#blaster (gen-cex: 0) (solve-result: 1) [∀ (x y : BLS12_381_G1_Element), bls12_381_G1_equal x y = true]

end Cryptograph.BLS12_381.SymbolicPoints
