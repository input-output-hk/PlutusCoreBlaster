import Cryptograph.FFI.Hash
import Cryptograph.FFI.Ed25519
import Cryptograph.FFI.Secp256k1
import Cryptograph.FFI.BLS12_381

/-!
# `Cryptograph.FFI`

Native-backed alternative to the pure-Lean `Cryptograph.*` library.
Binds, via `@[extern]`, to the same upstream C symbols that the
Haskell Plutus evaluator reaches through its `foreign import ccall`
declarations:

* **libsodium** — SHA-256, Blake2b-224/256, Ed25519 verify.
* **vendored crypton cbits** — SHA3-256, Keccak-256, RIPEMD-160.
* **libsecp256k1** — ECDSA verify, Schnorr verify.
* **blst** — BLS12-381 G1/G2/pairing suite.

Covers every cryptographic UPLC builtin. Each module exposes both a
`ByteArray`-typed primary function and a thin `List UInt8` wrapper
that is signature-compatible with the corresponding pure
`Cryptograph.*` definition.
-/
