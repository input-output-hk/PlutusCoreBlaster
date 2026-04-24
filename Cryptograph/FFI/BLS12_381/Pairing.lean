import Cryptograph.FFI.BLS12_381.G1
import Cryptograph.FFI.BLS12_381.G2

/-!
# Native-backed BLS12-381 pairing / miller-loop operations

Exposes the Plutus UPLC builtins `Bls12_381_millerLoop`,
`Bls12_381_mulMlResult`, and `Bls12_381_finalVerify`. `MlResult` is an
opaque Lean wrapper around a heap-allocated `blst_fp12`.

C symbols bound here are `lean_plutus_bls_miller_loop`,
`lean_plutus_bls_mul_ml_result`, `lean_plutus_bls_final_verify`, which
delegate to `blst_miller_loop`, `blst_fp12_mul`, `blst_fp12_finalverify`
respectively.
-/

namespace Cryptograph.FFI.BLS12_381

private opaque MlResultPointed : NonemptyType
/-- Miller-loop output (an element of Fp12 in the pairing target
    group). Not directly inspectable; combined with other `MlResult`
    values via `Pairing.mulMlResult` and consumed by
    `Pairing.finalVerify`. -/
def MlResult : Type := MlResultPointed.type
instance : Nonempty MlResult := MlResultPointed.property

namespace Pairing

/-- Miller loop of a G1 and a G2 point. Plutus' convention (as in
    `Cardano.Crypto.EllipticCurve.BLS12_381.Internal.millerLoop`) is
    to take the G1 point first. -/
@[extern "lean_plutus_bls_miller_loop"]
opaque millerLoop (p : @& G1Point) (q : @& G2Point) : MlResult

@[extern "lean_plutus_bls_mul_ml_result"]
opaque mulMlResult (a b : @& MlResult) : MlResult

@[extern "lean_plutus_bls_final_verify"]
opaque finalVerify (a b : @& MlResult) : Bool

end Pairing

end Cryptograph.FFI.BLS12_381
