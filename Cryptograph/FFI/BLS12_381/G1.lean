/-!
# Native-backed BLS12-381 G1 operations

All declarations below bind the matching C shim in
`Cryptograph/FFI/c/lean_plutus_bls12_381.c`, which in turn calls the
blst (supranational/blst) symbols used by
`Cardano.Crypto.EllipticCurve.BLS12_381.Internal`.

`G1Point` is an opaque Lean wrapper around a heap-allocated jacobian
`blst_p1` that is freed when the wrapping Lean value is collected.
-/

namespace Cryptograph.FFI.BLS12_381

@[extern "lean_plutus_bls_initialize"]
private opaque registerExternals : IO Unit

builtin_initialize registerExternals

private opaque G1PointPointed : NonemptyType
def G1Point : Type := G1PointPointed.type
instance : Nonempty G1Point := G1PointPointed.property

namespace G1

@[extern "lean_plutus_bls_g1_add"]
opaque add (a b : @& G1Point) : G1Point

@[extern "lean_plutus_bls_g1_neg"]
opaque neg (p : @& G1Point) : G1Point

/-- Scalar multiplication. `scalar` is a big-endian byte string; it may
    be up to 32 bytes (shorter values are left-padded with zeros). -/
@[extern "lean_plutus_bls_g1_scalar_mul"]
opaque scalarMul_bytes (scalar : @& ByteArray) (p : @& G1Point) : G1Point

@[extern "lean_plutus_bls_g1_equal"]
opaque equal (a b : @& G1Point) : Bool

/-- Serialize a G1 point in 48-byte compressed form (BLS12-381 spec). -/
@[extern "lean_plutus_bls_g1_compress"]
opaque compress_bytes (p : @& G1Point) : ByteArray

/-- Parse a 48-byte compressed encoding. Returns `Except String G1Point`,
    with a human-readable error on bad length, bad encoding, or a point
    that is not in the prime-order subgroup. -/
@[extern "lean_plutus_bls_g1_uncompress"]
opaque uncompress_bytes (bytes : @& ByteArray) : Except String G1Point

/-- `hash_to_curve(msg, dst)` with the caller-supplied domain-separation
    tag; Plutus does not pin the DST. -/
@[extern "lean_plutus_bls_g1_hash_to_group"]
opaque hashToGroup_bytes (msg dst : @& ByteArray) : G1Point

end G1

end Cryptograph.FFI.BLS12_381
