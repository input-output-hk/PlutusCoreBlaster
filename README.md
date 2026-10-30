# PlutusCoreBlaster

[![Lean Version](https://img.shields.io/badge/Lean-v4.24.0-blue.svg)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Contributions Welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg)](#contributing)

PlutusCoreBlaster is a Lean 4 formalization of [Untyped Plutus Core (UPLC)](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf), the smart contract execution language of Cardano. It provides UPLC syntax, decoders, a CEK evaluator, builtin functions, tests, and tools for preparing programs for proofs. The project is working toward conformance with the Haskell reference implementation; see [Conformance testing](#conformance-testing) for the current scope.

## Contents

- [Installation and building](#installation-and-building)
- [Using the library](#using-the-library)
- [Libraries and modules](#libraries-and-modules)
- [Preparing a UPLC program](#preparing-a-uplc-program)
- [Testing](#testing)
- [Conformance testing](#conformance-testing)
- [Benchmarks](#benchmarks)
- [Current scope](#current-scope)
- [Contributing](#contributing)

## Installation and building

Install z3 version 4.15.2.
Install Lean 4 through [elan](https://github.com/leanprover/elan). The version selected by this repository is recorded in [`lean-toolchain`](lean-toolchain) (currently 4.24.0). Lake fetches the [Lean-blaster](https://github.com/input-output-hk/Lean-blaster) dependency; the `Cryptograph` library is included in this repository.

```sh
lake build          # build the default PlutusCore target
lake build Lemmas   # build the proof library
lake test           # build the standard test suite
```

The corresponding Make targets are `make build_plutus_core`, `make build_tests`, and `make check_all`. The `check_*` targets also check that the expected Lean files are covered by their builds.

## Using the library

The Lake package is named **`PlutusCore`**, while the Git repository is named `PlutusCoreBlaster`. Add it to your project's Lake configuration in either format:

```toml
# lakefile.toml
[[require]]
name = "PlutusCore"
git = "https://github.com/input-output-hk/PlutusCoreBlaster"
rev = "main"
```

```lean
-- lakefile.lean
require «PlutusCore» from git
  "https://github.com/input-output-hk/PlutusCoreBlaster" @ "main"
```

For reproducible builds, replace `main` with a commit or release tag that you have tested.

## Libraries and modules

| Library or module | Purpose |
| --- | --- |
| `PlutusCore.UPLC.Term` | UPLC terms, programs, constants, and builtin names |
| `PlutusCore.UPLC.CekMachine` | CEK evaluation with a step limit or an execution budget |
| `PlutusCore.UPLC.BuiltinFunctions` | Arithmetic, byte strings, cryptography, data, lists, pairs, and bitwise operations |
| `PlutusCore.UPLC.TextEncoding` | Parser for textual `.uplc` programs |
| `PlutusCore.UPLC.FlatEncoding` | Decoder for Flat-encoded programs |
| `PlutusCore.UPLC.ScriptEncoding` | Decoders and import commands for Flat, CBOR-wrapped, hexadecimal, and textual scripts |
| `PlutusCore.UPLC.PlutusScript` | Script envelope and Plutus V1/V2/V3 language tags |
| `PlutusCore.UPLC.PreProcess` | `#prep_uplc` command for preparing proof and execution expressions |
| `Cryptograph` | Bundled BLS12-381, Ed25519, Secp256k1, hash, and modular arithmetic code |
| `Lemmas` | Proofs and helper lemmas for the formalization |

The CEK machine has four states: `Eval`, `Return`, `Error`, and `Halt`. Its step-limited execution and budget-aware execution use the same UPLC model. Some newer array and value/coin features are not implemented yet; see [Current scope](#current-scope).

The convenience `IsData String` instance and generated text-field codecs use
UTF-8 bytes in `Data.B`; decoding rejects invalid UTF-8. A claim quantified over
`String` covers valid UTF-8 text only. Use `ByteString` or raw `Data` for properties
that must cover arbitrary payloads, including invalid UTF-8. Native UPLC
`#string` arguments remain `Const.String`; the compiled-interface profile rejects
native strings nested inside Data containers and keeps runtime inputs as raw
`Data`.

## Preparing a UPLC program

`#prep_uplc` takes a named `PlutusScript`, an optional input-conversion function, and a maximum number of CEK steps. It creates a named structure with `lang`, `prop` (the optimized expression for proofs), and `exec` (the original expression for execution). For example, this closed program is adapted from [`PlutusCore/UPLC/PreProcess/Tests.lean`](PlutusCore/UPLC/PreProcess/Tests.lean):

```lean
import PlutusCore.UPLC.PreProcess

open PlutusCore.UPLC.PlutusScript (PlutusScript)
open PlutusCore.UPLC.Term (Program Version Term Const)

def answerScript : PlutusScript :=
  { lang := .PlutusV3
    script := Program.Program (Version.Version 1 1 0)
      (Term.Const (Const.Integer 42)) }

#prep_uplc preparedAnswer answerScript 10
#check preparedAnswer.prop
#check preparedAnswer.exec
```

The final number is a **step limit**, not a CPU or memory `ExBudget`. Programs that take inputs can provide an input-conversion function before that number; see the syntax and example in [`PreProcess.lean`](PlutusCore/UPLC/PreProcess.lean).

## Testing

```sh
lake test
# or: make build_tests
```

The standard `Tests` target covers encoding and CBOR, bitwise operations, CEK execution, preprocessing, cryptographic vectors, and equality. It includes textual UPLC parser tests. It does **not** run the generated conformance suite.

## Conformance testing

The generator in [`scripts/GenConformanceTests.lean`](scripts/GenConformanceTests.lean) derives Lean cases from the [Plutus conformance corpus](https://github.com/IntersectMBO/plutus/tree/master/plutus-conformance). The generated tests compare evaluation results and execution budgets with the reference expectations. Categories that rely on features not yet implemented can be excluded during generation (including array and value/coin operations).

The conformance suite needs the external Plutus corpus at `.plutus-conformance/plutus-conformance`. After providing that path, run:

```sh
make gen_conformance_tests excludeNotImplemented=1
make check_conformance
```

The [conformance workflow](.github/workflows/ci-conformance.yaml) runs separately from the normal CI. A maintainer can trigger it on a PR with `/run-conformance` or run it manually. A passing `lake test` does not imply that all conformance cases pass.

## Benchmarks

The `#prep_uplc` benchmark suite measures preprocessing time and memory and can compare two runs. See [`Benchmark/README.md`](Benchmark/README.md) for requirements, case selection, commands, and result fields.

```sh
make build_benchmark
make bench_prep_uplc BENCH_ARGS="--suite repo,symbolic"
```

## Current scope

| Component | State |
| --- | --- |
| UPLC syntax and CEK evaluation | Implemented; the budgeted evaluator's termination proof is pending |
| Text, Flat, and script decoding | Implemented for supported UPLC features |
| Builtin functions and cryptographic primitives | Implemented for supported batches; array and value/coin features remain open |
| Standard tests | Built by `lake test` |
| Formal proofs in `Lemmas` | In progress |
| Reference conformance | Generated and checked separately; unsupported categories can be excluded |

## Contributing

Bug reports, documentation improvements, tests, and code changes are welcome. Open an [issue](https://github.com/input-output-hk/PlutusCoreBlaster/issues) to discuss a problem or submit a pull request. Before submitting code, run `make check_all`; changes affecting reference behavior may also need a conformance run.

Maintainers: [Jean-Frédéric Etienne](https://github.com/etiennejf), [Romain Soulat](https://github.com/RSoulatIOHK), and [Mark Petruska](https://github.com/mpetruska).

The coordinated assurance runner revision-checks the sibling repositories, then
selects them using ignored `.lake/package-overrides.json` files. Normal consumers
use the Git dependency pinned in `lakefile.lean` and `lake-manifest.json` and need
no sibling checkout. Remove local overrides to return to the published pins.
The runner rejects existing conflicting overrides instead of replacing them.
