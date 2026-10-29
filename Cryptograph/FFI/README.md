# Native hashes and Ed25519

The compiled Plutus APIs use native implementations for:

| Primitive | Provider |
|---|---|
| SHA-256, Blake2b-224, Blake2b-256, Ed25519 verification | libsodium |
| SHA3-256, Keccak-256, RIPEMD-160 | vendored crypton C |

The C bridge is adapted from [PR13](https://github.com/input-output-hk/PlutusCoreBlaster/pull/13),
revision `b12153961f282a855d918a69fb05209a8f0786b6`. This slice wires those primitives into
Lake, the public Plutus wrappers, the native benchmark and CI. Secp256k1 and BLS remain on
their existing Lean implementations; PR13 contains work toward their native backends.

## Build and test

Install a native C toolchain, `pkg-config`, and libsodium development files:

```sh
# Debian/Ubuntu
sudo apt-get install libsodium-dev pkg-config
# macOS
brew install libsodium pkg-config

lake build bench_cek test_crypto_ffi
python3 scripts/test_crypto_ffi.py
python3 scripts/test_bench_cek.py --benchmark-root /path/to/plutus-vm-benchmark --profile-corpus
```

`pkg-config` supplies the include and link flags. It must select the target architecture's
installation. When changing prefixes, rerun `lake -R` and clean old native artifacts. On Apple
Silicon with both Intel and ARM Homebrew installations, for example:

```sh
PKG_CONFIG_PATH=/opt/homebrew/opt/libsodium/lib/pkgconfig lake -R build bench_cek test_crypto_ffi
```

libsodium is dynamically linked and is also needed at runtime. Build and runtime versions
must be compatible. `builtin_initialize` calls `sodium_init` and propagates initialization
failure. Inputs are borrowed ByteArrays; hash outputs are newly allocated Lean ByteArrays.
The bridge preserves Plutus's one-byte-per-character ByteString representation, including
non-ASCII bytes, embedded NULs and the reference's low-byte conversion of arbitrary characters.
It does not hash the UTF-8 representation of a ByteString.

## Logical interface

The public `opaque` functions and their types remain in `PlutusCore.Crypto.Hash` and
`PlutusCore.Crypto.Ed25519`. `@[implemented_by]` selects native wrappers for compiled execution.
Their bodies call the exported `*Reference` definitions. Raw `@[extern]` bindings also have
Lean bodies. This change adds no crypto axioms and proves no C/Lean equivalence theorem.
Conformity checks are executable tests; no new proof uses `native_decide`.

The existing pure functions in `Cryptograph.*` are still available. Public Plutus reference
functions are `sha2_256Reference`, `sha3_256Reference`, `blake2b_224Reference`,
`blake2b_256Reference`, `keccak_256Reference`, `ripemd_160Reference`, and
`verifyEd25519SignatureReference`.

Two reference bugs exposed by the boundary tests are corrected:

- RIPEMD-160's Nat subtraction lost a padding block for lengths 56–62 modulo 64.
- Ed25519 used a cofactored verification equation and accepted small-order forgeries.
  It now rejects small-order keys/nonces and uses the uncofactored equation, matching
  libsodium's single-signature verification. Public key/signature length failures retain
  their existing Plutus evaluation errors; other invalid signatures return `false`.

`test_crypto_ffi.py` compares all six native hash APIs with their Lean references, plus
independent hashlib outputs and fixed Keccak vectors. Cases cross block, padding and rate
boundaries and exercise every byte value. Ed25519 checks the pinned 210-case Wycheproof corpus,
plus public API length failures and the identity forgery. For Wycheproof's `acceptable` cases,
the test requires native/reference agreement; it does not impose a separate acceptance policy.
See `Tests/Crypto/FFI/README.md` for provenance and license.

Use the uninstrumented `bench_cek time` command to compare performance with the base revision;
use `profile` to explain where time remains. File I/O and formatting stay outside benchmark
timers, and CPU/memory ledger ExUnits are unchanged by the native implementation.
