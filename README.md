# PlutusCoreBlaster

[![Lean Version](https://img.shields.io/badge/Lean-v4.24.0-blue.svg)](https://github.com/leanprover/lean4)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Contributions Welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg)](CONTRIBUTING.md)

A Lean 4 formalization of [Untyped Plutus Core (UPLC)](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf) — the smart contract execution language of the Cardano blockchain.

The goal is a machine-checked specification that is **provably conformant** with the Haskell reference implementation, verified against the official Plutus conformance test suite.

## Table of Contents

- [PlutusCoreBlaster](#plutuscoreblaster)
  - [Table of Contents](#table-of-contents)
  - [Installation](#installation)
    - [Prerequisites](#prerequisites)
    - [Installing Lean4](#installing-lean4)
    - [Building](#building)
  - [How to use?](#how-to-use)
    - [Using lakefile.toml](#using-lakefiletoml)
    - [Using lakefile.lean](#using-lakefilelean)
  - [Features](#features)
    - [PlutusCore library](#plutuscore-library)
    - [Cryptograph library](#cryptograph-library)
    - [Lemmas library](#lemmas-library)
  - [The #prep\_uplc command](#the-prep_uplc-command)
  - [Tests](#tests)
  - [General description](#general-description)
    - [CEK machines](#cek-machines)
    - [Builtin functions](#builtin-functions)
    - [Encoding formats](#encoding-formats)
  - [Status](#status)
  - [Contributing](#contributing)
    - [Ways to Contribute](#ways-to-contribute)


## Installation

### Prerequisites

PlutusCoreBlaster requires:

- **Lean4** v4.24.0 (or compatible version)

All other dependencies (`Cryptograph`, `Blaster`) are either bundled in this repository or fetched automatically by `lake`.

### Installing Lean4

We strive to stay in sync with the latest **stable release** of Lean4.

**Currently supported version:** Lean4 v4.24.0

Please follow the official installation guidelines from the [Lean4 GitHub repository](https://github.com/leanprover/lean4).

### Building

```bash
lake build
```

To run the test suite:

```bash
lake build Tests
```

## How to use?

In order to use PlutusCoreBlaster as a library, your project needs to depend on it.

### Using lakefile.toml

```toml
[[require]]
name = "PlutusCore"
git = "https://github.com/input-output-hk/PlutusCoreBlaster"
rev = "main"
```

### Using lakefile.lean

```lean
require «PlutusCore» from git
  "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"
```

## Features

### PlutusCore library

| Module | What it formalizes |
|--------|--------------------|
| `UPLC/Term` | Abstract syntax: the 9 UPLC term constructors, builtin types, and constants (integers, byte strings, BLS12-381 elements, …) |
| `UPLC/CekMachine` | Budget-aware CEK abstract machine — frames, stack, states (`Eval`, `Return`, `Error`, `Halt`) |
| `UPLC/CekValue` | Runtime value types (`VCon`, `VLam`, `VDelay`, `VConstr`, `VBuiltin`) and environments |
| `UPLC/ExBudget` | CPU and memory budget types with saturation arithmetic |
| `UPLC/CostModels` | Per-step cost functions (CEK machine steps + per-builtin costs) |
| `UPLC/BuiltinFunctions` | ~50 builtin implementations: integer arithmetic, byte-string ops, cryptography, list/pair/data operations, bitwise ops |
| `UPLC/FlatEncoding` | Bit-level decoder for the compact flat binary format (Appendix C of the spec) |
| `UPLC/ScriptEncoding` | CBOR/hex script encoding used for on-chain storage |
| `UPLC/PlutusScript` | `PlutusLanguage` (V1/V2/V3) and `PlutusScript` envelope wrapping a UPLC program |
| `UPLC/PreProcess` | `#prep_uplc` command — optimizes and compiles a `PlutusScript` for formal verification |
| `UPLC/Utils` | Helper predicates and accessors over CEK machine states |
| `Bitwise` | Bitwise byte-string operations (and/or/xor/complement, shifts, rotates, bit read/write) |

### Cryptograph library

The `Cryptograph` library is bundled in this repository and provides all cryptographic primitives used by UPLC builtins:

| Module | What it provides |
|--------|-----------------|
| `BLS12_381` | G1/G2 point arithmetic and pairing |
| `Ed25519` | Edwards curve field, points, and signature verification |
| `Secp256k1` | ECDSA and Schnorr signature verification |
| `Sha2` | SHA-256 and SHA-512 |
| `Sha3` | SHA3-256 |
| `Keccak` | Keccak-256 |
| `Ripemd` | RIPEMD-160 |
| `Blake2b` | BLAKE2b |
| `Integer` | Modular exponentiation |

### Lemmas library

Formal proofs and helper lemmas about the encoding/decoding functions.

## The #prep_uplc command

`#prep_uplc` is a Lean 4 command that takes a `PlutusScript` instance, optimizes the embedded UPLC program using [Blaster](https://github.com/input-output-hk/Lean-blaster)'s expression optimizer, and generates a `PrepUPLC` structure containing:

- **`prop`** — the optimized UPLC expression, suitable as a proof obligation
- **`exec`** — the original unoptimized expression, used for execution

```lean
-- Define a Plutus script
def myScript : PlutusScript := {
  lang := .PlutusV3,
  script := <your UPLC program>
}

-- Compile it for formal verification (budget limit: 500 steps)
#prep_uplc myCompiledScript myScript 500

-- The generated PrepUPLC instance exposes:
-- myCompiledScript.prop  ← optimized, ready for proof
-- myCompiledScript.exec  ← original, ready for execution
```

## Tests

The `Tests` library covers:

- **Encoding round-trips** — flat and script (CBOR/hex) encoding correctness
- **Bitwise operations** — byte-string bitwise op correctness
- **CBOR** — CBOR encoding/decoding correctness
- **Cryptographic test vectors** — BLS12-381, BLAKE2b, Keccak-256, RIPEMD-160, SHA-256, SHA-512, SHA3-256

```bash
lake build Tests
```

## General description

PlutusCoreBlaster formalizes UPLC evaluation in three layers: syntax, machine, and builtins.

### CEK machines

The CEK machine (`UPLC/CekMachine`) implements the standard CEK machine as specified in the Plutus Core specification. Evaluation proceeds through four states:

Two version are delivered:
- **Budget-aware CEK** — tracks an `ExBudget` and halts with an error if the budget is exceeded
- **Step-counting CEK** — ignores budgets and simply counts the number of steps taken

### Builtin functions

`UPLC/BuiltinFunctions` provides implementations of all ~50 builtins, except the newer around `coins` and `arrays`, including:

- Integer arithmetic and comparison
- Byte-string operations
- Cryptographic primitives (see `Cryptograph`)
- List, pair, and data constructors/destructors
- Bitwise operations

### Encoding formats

PlutusCoreBlaster supports the two binary wire formats used in the Plutus ecosystem:

- **Flat** (`.flat`) — compact binary format decoded by `UPLC/FlatEncoding`, specified in Appendix C of the spec
- **Script** — CBOR-wrapped flat encoding used for on-chain storage, handled by `UPLC/ScriptEncoding`

## Status

| Component | Status |
|-----------|--------|
| UPLC syntax & values | ✅ Complete |
| CEK machine (budget-aware) | ✅ Complete |
| Builtin functions (Batches 1–7) | ✅ Complete |
| Flat / script encoding | ✅ Complete |
| Cryptographic primitives | ✅ Complete |
| PlutusScript + #prep_uplc | ✅ Complete |
| Encoding tests | ✅ Passing |
| Formal proofs (Lemmas) | 🚧 In progress |
| Conformance tests | 🚧 In progress |

## Contributing

We welcome all contributions! Whether it's bug reports, feature requests, documentation improvements, or code contributions, your help is appreciated.

### Ways to Contribute

- Report bugs and issues
- Suggest new features or improvements
- Improve documentation
- Submit pull requests

**Maintained by:**
- [Jean-Frédéric Etienne](https://github.com/etiennejf)
- [Romain Soulat](https://github.com/RSoulatIOHK)
- [Mark Petruska](https://github.com/mpetruska)

**Questions?** Feel free to [open an issue](https://github.com/input-output-hk/PlutusCoreBlaster/issues) or reach out to the maintainers.
