import Cryptograph.FFI.Sha2.Sha256
import Cryptograph.FFI.Sha3.Sha3_256
import Cryptograph.FFI.Blake2b.Blake2b
import Cryptograph.FFI.Keccak.Keccak256
import Cryptograph.FFI.Ripemd.Ripemd160
import Cryptograph.FFI.Ed25519
import Cryptograph.FFI.Secp256k1
import Cryptograph.FFI.BLS12_381

/-!
# `Cryptograph.FFI`

Native-backed alternative to the pure-Lean `Cryptograph.*` library.
Each FFI module mirrors the namespace shape of its pure twin so a
call-site can swap implementations by swapping one
`import` / `open` — e.g. `Cryptograph.Sha2.Sha256.hashBytes` and
`Cryptograph.FFI.Sha2.Sha256.hashBytes` are interchangeable.

For BLS12-381, the pure and FFI carrier types differ; the
`Cryptograph.BLS12_381.BlsBackend` typeclass abstracts over both.
Either of the `pureBackend` / `ffiBackend` instances satisfies it.

C symbol bindings (each defined under `Cryptograph/FFI/c/*.c`) target
the same upstream C functions the Haskell Plutus evaluator uses:

* **libsodium** — SHA-256, Blake2b-224/256, Ed25519 verify.
* **vendored crypton cbits** — SHA3-256, Keccak-256, RIPEMD-160.
* **libsecp256k1** — ECDSA verify, Schnorr verify.
* **blst** — BLS12-381 G1/G2/pairing suite.
-/
