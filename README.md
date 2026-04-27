# PlutusCoreBlaster

A Lean 4 formalization of [Untyped Plutus Core (UPLC)](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf) — the smart contract execution language of the Cardano blockchain.

The goal is a machine-checked specification that is **provably conformant** with the Haskell reference implementation, verified against the official Plutus conformance test suite.

## What's in here

### `PlutusCore` library

| Module | What it formalizes |
|--------|--------------------|
| `UPLC/Term` | Abstract syntax: the 9 UPLC term constructors, builtin types, and constants (integers, byte strings, BLS12-381 elements, …) |
| `UPLC/CekMachine` | Budget-aware CEK abstract machine — frames, stack, states (`Eval`, `Return`, `Error`, `Halt`) |
| `UPLC/CekValue` | Runtime value types (`VCon`, `VLam`, `VDelay`, `VConstr`, `VBuiltin`) and environments |
| `UPLC/ExBudget` | CPU and memory budget types with saturation arithmetic |
| `UPLC/CostModels` | Per-step cost functions (CEK machine steps + per-builtin costs) |
| `UPLC/BuiltinFunctions` | ~50 builtin implementations: integer arithmetic, byte-string ops, cryptography, list/pair/data operations, bitwise ops |
| `UPLC/TextEncoding` | Parser for the standard `.uplc` text format (full grammar, Haskell-style literals) |
| `UPLC/FlatEncoding` | Bit-level decoder for the compact flat binary format (Appendix C of the spec) |
| `UPLC/ScriptEncoding` | CBOR/hex script encoding used for on-chain storage |
| `Crypto` | BLS12-381 G1/G2/pairing, SHA-2/SHA-3/Keccak/BLAKE2b/RIPEMD-160, Ed25519, Secp256k1 ECDSA/Schnorr, modular exponentiation |
| `Bitwise` | Bitwise byte-string operations (and/or/xor/complement, shifts, rotates, bit read/write) |
| `Parser` | Monadic parser infrastructure shared by the text encoder |

### `Tests` library

- **Unit tests** — encoding round-trips for flat, script, and text formats; bitwise and CBOR correctness
- **Conformance tests** — 1 134 auto-generated test cases derived from the official [Plutus conformance test suite](https://github.com/input-output-hk/plutus/tree/master/plutus-conformance), covering:
  - `Generated/Term/` — all 9 term constructors (Lam, Apply, Delay, Force, Const, Var, Constr, Case, Error)
  - `Generated/Builtin/` — every builtin function across all Plutus batches 1–7
  - `Generated/Example/` — real-world script examples

Each conformance test loads a `.uplc` program, runs it through the CEK machine, and checks:
1. The result value is alpha-equivalent to the reference output
2. The CPU and memory budget consumed matches the reference exactly

### `Lemmas` library

Formal proofs and helper lemmas about the encoding/decoding functions.

## Building

**Prerequisites**: [Lean 4.24.0](https://leanprover.github.io/lean4/doc/setup.html) via `elan`, and the [`Cryptograph`](https://github.com/input-output-hk/Cryptograph) library checked out alongside this repo.

```bash
# Expected directory layout:
#   ../Cryptograph/   ← Cryptograph library
#   ../PlutusCoreBlaster/   ← this repo

lake build
```

To run the test suite:
```bash
lake build Tests
```

## Conformance

The conformance tests are generated from the Plutus reference test corpus using `gen_conformance_tests.py`. Each test is a Lean `#eval` that asserts evaluation equivalence and budget equality against the Haskell reference output:

```lean
-- Tests/Conformance/Generated/Term/Lam/Lam_1.lean
#eval programsEvalEquiv term_lam_lam_1 term_lam_lam_1_expected
#eval! budgetMatches term_lam_lam_1 16100 200  -- CPU=16100, Memory=200
```

A passing `lake build Tests` means the Lean formalization agrees with the reference implementation on every test case.

## Relationship to `sc-fvt`

This repository contains the `PlutusCore` sub-project extracted from [input-output-hk/sc-fvt](https://github.com/input-output-hk/sc-fvt), which also formalizes `PlutusTx`, `PlutusLedgerAPI`, and a solver. `PlutusCoreBlaster` is the standalone, publicly reviewable home for the core UPLC formalization.

## Status

| Component | Status |
|-----------|--------|
| UPLC syntax & values | ✅ Complete |
| CEK machine (budget-aware) | ✅ Complete |
| Builtin functions (Batches 1–7) | ✅ Complete |
| Text / flat / script encoding | ✅ Complete |
| Conformance tests (1 134 cases) | ✅ Passing |
| Formal proofs (Lemmas) | 🚧 In progress |
