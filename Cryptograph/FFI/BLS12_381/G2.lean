import Cryptograph.FFI.BLS12_381.G1

/-!
# Native-backed BLS12-381 G2 operations

Mirror of `Cryptograph.FFI.BLS12_381.G1` over the twisted curve. Bytes
in compressed form are 96 bytes (not 48). All extern symbols resolve
to `lean_plutus_bls_g2_*` shims backed by `blst_p2_*` from blst.
-/

namespace Cryptograph.FFI.BLS12_381

private opaque G2PointPointed : NonemptyType
def G2Point : Type := G2PointPointed.type
instance : Nonempty G2Point := G2PointPointed.property

namespace G2

@[extern "lean_plutus_bls_g2_add"]
opaque add (a b : @& G2Point) : G2Point

@[extern "lean_plutus_bls_g2_neg"]
opaque neg (p : @& G2Point) : G2Point

@[extern "lean_plutus_bls_g2_scalar_mul"]
opaque scalarMul_bytes (scalar : @& ByteArray) (p : @& G2Point) : G2Point

@[extern "lean_plutus_bls_g2_equal"]
opaque equal (a b : @& G2Point) : Bool

/-- Serialize a G2 point in 96-byte compressed form. -/
@[extern "lean_plutus_bls_g2_compress"]
opaque compress_bytes (p : @& G2Point) : ByteArray

@[extern "lean_plutus_bls_g2_uncompress"]
opaque uncompress_bytes (bytes : @& ByteArray) : Except String G2Point

@[extern "lean_plutus_bls_g2_hash_to_group"]
opaque hashToGroup_bytes (msg dst : @& ByteArray) : G2Point

end G2

end Cryptograph.FFI.BLS12_381
