# PlutusCoreBlaster

A Lean 4 formalisation of Plutus Core (UPLC) and its cryptographic
primitives. Includes:

- `PlutusCore/` — UPLC term language and semantics.
- `Cryptograph/` — pure-Lean reference implementations of every
  cryptographic UPLC builtin (SHA2-256, SHA3-256, Blake2b-224/256,
  Keccak-256, RIPEMD-160, Ed25519 verify, ECDSA/Schnorr secp256k1
  verify, BLS12-381).
- `Cryptograph/FFI/` — native-backed alternative of the same surface,
  binding via `@[extern]` to the identical C symbols the Haskell
  Plutus evaluator reaches through `foreign import ccall`.
- `Lemmas/`, `Tests/` — proofs and test vectors.

## Build

```bash
make build_all       # PlutusCore + Cryptograph + Tests
make build_tests     # just the test library
lake build           # raw lake — everything
lake test            # raw lake — Tests library
```

The `make` targets auto-detect your build environment and put
libsodium / libsecp256k1 / libblst on the compiler/linker path
either via your system package manager (no Nix involvement) or via
`nix-shell --run` if you have Nix installed. See
[Cryptograph.FFI native dependencies](#cryptographffi-native-dependencies)
for the two install paths.

Without those native libraries installed, `lake build` still
compiles every Lean source file. The four `extern_lib` targets that
wrap `Cryptograph.FFI.*` only become buildable once their native
dependencies are present — until then they fail at the C-compile
step. The pure `Cryptograph.*` modules are unaffected.

## Toolchain

- Lean / Lake: pinned by [`lean-toolchain`](lean-toolchain)
  (managed by `elan`).
- A C compiler (`cc`, usually clang or gcc) — used by Lake to build
  the FFI shims.

## `Cryptograph.FFI` native dependencies

`Cryptograph.FFI` binds to the **same upstream C libraries** the
Haskell Plutus evaluator uses. They must be installed on the host
(headers + runtime) before the corresponding `extern_lib` target
can compile:

| `extern_lib` target    | Library        | Provides                                   |
| ---------------------- | -------------- | ------------------------------------------ |
| `leanPlutusHash`       | **libsodium**  | SHA-256, Blake2b-224/256                   |
| `leanPlutusHash`       | *(vendored)*   | SHA3-256, Keccak-256, RIPEMD-160 — ships as crypton cbits under [Cryptograph/FFI/c/crypton/](Cryptograph/FFI/c/crypton/); no extra install |
| `leanPlutusEd25519`    | **libsodium**  | Ed25519 detached-signature verification    |
| `leanPlutusSecp256k1`  | **libsecp256k1** | ECDSA + Schnorr (BIP-340) verification   |
| `leanPlutusBls12_381`  | **libblst**    | BLS12-381 G1/G2/pairing (from [supranational/blst](https://github.com/supranational/blst)) |

### Install

Pick **one** of the two install paths below. The `make` targets
auto-detect which you used: if libsodium and libsecp256k1 are on the
system's `pkg-config` path (or you're already inside a `nix-shell`),
they invoke `lake` directly; otherwise they fall back to
`nix-shell --run` when `nix-shell` is on `PATH`. To force a specific
behaviour, override `NIX_RUN`, e.g.
`make NIX_RUN='nix-shell --run' build_all` or `make NIX_RUN= build_all`.

#### Option A — system packages

**Arch Linux**

```bash
sudo pacman -S libsodium libsecp256k1
# libblst lives in the AUR:
paru -S blst                 # or: yay -S blst / aurutils / manual PKGBUILD
```

**Debian / Ubuntu**

```bash
sudo apt install libsodium-dev libsecp256k1-dev
# libblst is not packaged; build from source (see below).
```

**macOS (Homebrew)**

```bash
brew install libsodium secp256k1
# libblst: build from source (see below).
```

**libblst from source** (pinned to the release Cardano uses):

```bash
git clone https://github.com/supranational/blst
cd blst && ./build.sh
sudo install -m644 libblst.a                  /usr/local/lib/
sudo install -m644 bindings/blst.h            /usr/local/include/
sudo install -m644 bindings/blst_aux.h        /usr/local/include/
sudo ldconfig
```

#### Option B — Nix

A [`shell.nix`](shell.nix) at the repo root pulls in pinned versions
of libsodium, libsecp256k1, and libblst (plus `pkg-config`). Either
enter the shell before building, or let `make` wrap commands for you:

```bash
nix-shell            # drops you into the dev shell, then `lake build` / `make build_all`
# or, without entering the shell:
make build_all       # auto-wraps each lake call in `nix-shell --run`
```

Nix sets `NIX_CFLAGS_COMPILE` / `NIX_LDFLAGS` automatically so `cc`
finds the headers and linker finds the libraries — no further
configuration is needed.

### Verify

```bash
lake build leanPlutusHash leanPlutusEd25519 \
           leanPlutusSecp256k1 leanPlutusBls12_381
```

All four static libraries must build cleanly. If a target fails with
`fatal error: <header>.h: No such file or directory`, the matching
dev package from the table above is missing.

## Layout reference

```
Cryptograph/
├── …                              (pure-Lean reference implementations)
└── FFI/
    ├── FFI.lean                   (public re-export)
    ├── Hash.lean                  (sha2_256, blake2b_*, sha3_256, keccak_256, ripemd_160)
    ├── Ed25519.lean               (verify)
    ├── Secp256k1.lean             (verifyEcdsa, verifySchnorr)
    ├── BLS12_381/
    │   ├── G1.lean  G2.lean  Pairing.lean
    │   └── BLS12_381.lean
    └── c/
        ├── lean_plutus_crypto.h
        ├── lean_plutus_{hash,ed25519,secp256k1,bls12_381}.c
        └── crypton/               (vendored from kazu-yamamoto/crypton)
            ├── crypton_sha3.{c,h}         (SHA3-256 and Keccak-256)
            ├── crypton_ripemd.{c,h}       (RIPEMD-160)
            └── crypton_{bitfn,align}.h    (shared helpers)
```
