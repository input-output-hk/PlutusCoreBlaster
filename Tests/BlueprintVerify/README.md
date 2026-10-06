# Generated UAL assurance verification

The legacy `Game` fixture originated from Plutus's
`doc/docusaurus/static/code/Example/Ual/Game/Main.hs`. It ports the on-chain
`isGoodGuess` rule from plutus-apps `Plutus.Contracts.Game.Alonzo` to current
Plinth. It does not rebuild the historical application's off-chain code or its
address-diversifying `GameParam`.

The three quantified claims constrain the imported compiled UPLC: a matching
SHA-256 hash succeeds; a nonmatching hash fails; an integer datum fails decoding.
Hashing is opaque to SMT. No collision-freedom assumption is made. `Evaluate.lean`
separately executes the known SHA-256 vector for `hello` and a nonmatching guess.
The human-readable validator title deliberately differs from its stable id.

## Check the committed fixture

From this repository, with the locked dependencies and Lean/Z3 available:

```sh
lake build PlutusCore.UPLC.BlueprintEncoding.Assurance
lake env lean Tests/BlueprintVerify/Game/Check.lean
lake env lean Tests/BlueprintVerify/Game/Evaluate.lean
lake env lean Tests/BlueprintVerify/Regression.lean
lake env python3 Tests/BlueprintVerify/regression.py
```

## Compile, generate, and verify afresh

In a Plutus checkout containing the UAL generator and its normal build environment:

```sh
cabal build docusaurus-examples:exe:example-ual-game
cabal list-bin docusaurus-examples:exe:example-ual-game
```

Pass the resulting executable path to this command, from PlutusCoreBlaster:

```sh
lake env python3 Tests/BlueprintVerify/run_generated.py \
  --generator /absolute/path/to/example-ual-game \
  --plutus /absolute/path/to/plutus \
  --output /absolute/path/to/fresh-results
```

The runner regenerates both JSON files, runs all three properties and the concrete
vector, fails on skipped/failed checks, and writes the documents, logs, and
`run-report.json`, `verification-artifact.zip`, and `verified-assurance.json`.
The latter contains fresh `smt-check` evidence only after all checks pass. Each
record binds to the actual script hash and artifact digest. The report records the exact input hashes, generator binary and
source hashes, checker source hashes, repository revisions and tracked diff hashes,
Lean/Z3 versions, and explicit execution settings. It is a local run record, not a
signed attestation or a Lean kernel proof. Original generated claims remain in
`assurance.json`; evidence is written separately, with a precise method label.
It uses the Blaster checkout selected by this repository's `lake-manifest.json`.
The game needs no CardanoLedgerApi import. Ledger-dependent examples must record
and supply that additional package explicitly.

Do not reuse arbitrary precompiled modules or an unrelated `LEAN_PATH` when
reproducing evidence. Rebuild in a clean, pinned environment. The runner bounds
Lean processes; the solver has a 60-second timeout, distinct from preprocessing.
File SHA-256 checks use `sha256sum` or `shasum` from the trusted PATH, with a
pure Lean fallback. Pin these utilities as well as Z3 in a reproducible environment.
Third-party Lean sources require an OS sandbox since elaborators can execute code.

## Checking contract

`#verify_blueprint` validates the bundled CIP schema and its references, binds the
exact blueprint bytes and compiled script hashes, and reruns every executable
property regardless of old outcomes. It reports unsupported languages, URI-only
sources, and informal properties as not checked. The generated-example runner
requires all expected properties to verify; the general command permits clearly
reported non-executable claims alongside executable ones.

UAL 0.5 requires stable ids, explicit argument schemas, supported encodings, and
`budget: {"steps": n, "semantics": "A" | "B" | "C" | "D" | "E"}`.
A zero or insufficient step count is unfinished execution, not script rejection.
The current implementation supports `asData` and step budgets. It rejects Scott
encoding, ledger execution budgets, and unresolved or unguarded cyclic schemas.
The step bound is not a ledger execution-cost proof. Interpreter termination alone
is not a complete ledger-acceptance claim.

Only `def`/`abbrev` predicate fragments are accepted, per-property dependency
closures are isolated, admitted declarations/local axioms are rejected, and claims
must reference every scoped compiled program. This last check catches disconnected
specifications but cannot establish semantic relevance or rule out vacuity.
Assumptions must appear in the proposition; documentary assumptions are not axioms.

## Coordinated interface profile (UAL 0.6-draft)

The current game generator uses `writeInterfaceBundle` to emit the proposed
CIP-57 compiled-interface dialect and assurance-v2. `interface` contains ordered
parameter references and ledger runtime roles. Execution settings are in separate
`checking-<property>.json` artifacts. The profile checks evaluation outcomes under
an explicit CEK step bound; it does not establish ledger acceptance or deployment
binding.

The runner first captures the actual checking environment, then passes its path
to the generator. To use the generator directly, create a Lean driver with the
same imports used for checking:

```lean
import PlutusCore.UPLC.BlueprintEncoding.Assurance
#write_checking_environment "environment.json"
```

Run it with `lake env lean`, then run `example-ual-game environment.json`.
`example-ual-blueprint` (vesting) accepts the same argument. Ledger-dependent
properties require the relevant CardanoLedgerApi imports before capturing the
manifest and in the checking driver. Capturing an environment does not verify a
claim. The manifest pins loaded `.olean` files, the Lean and Z3 executables, and
solver options; the run artifact separately records source revisions and patches.
It is not a hermetic container/image description.

`#verify_blueprint` validates bundled schemas, exact context/environment digests,
target coverage, interface roles and language conventions. It constructs wrappers
independently for each property's selected context. Data and native encodings are
distinct; runtime inputs stay raw Data so malformed-input claims remain expressible.
Native `#list` and `#pair` bind raw Data elements; any narrower schema-domain
premises must be explicit in the proposition. A universal metadata label alone is
not proof of parameter coverage. The current profile rejects Scott encodings,
ledger-cost checking. Guarded recursive Data
parameters are supported without depth truncation.

Fresh `smt-check` evidence includes `checkingContextHash`. Changing settings makes
old evidence stale, even when the compiled template hash is unchanged. The old
UAL 0.5 game fixture remains available via the commands above. The fresh runner
uses the new format and a separate `EvaluateInterface.lean` vector test.

Additional checks:

```sh
lake env lean Tests/BlueprintVerify/NativeEncoding.lean
lake env python3 Tests/BlueprintVerify/interface_regression.py /path/to/fresh-results
```

The regression runner rejects altered contexts, mismatched environments, bad
interfaces, unsupported encodings and stale/incomplete bindings. It also checks
that zero steps cannot satisfy a success claim and that a false claim fails.

`Example/Ual/Parameters/Main.hs` is a second compiled integration example. Build
`docusaurus-examples:exe:example-ual-parameters`, then run:

```sh
lake env python3 Tests/BlueprintVerify/run_parameters.py /path/to/example-ual-parameters /path/to/results
```

It verifies the same integer rule through Data and native parameter boundaries,
then changes the native schema to Data while preserving the compiled bytes and
requires the claim to be falsified. This checks the producer-to-evaluator encoding
path, beyond metadata validation alone.

## Compiled assurance functions and detached Auction

`assurance-v2.json` can carry a `functions` registry. Functions have single-CBOR
Flat UPLC, a digest of the decoded bytes, ordered argument schemas and a result
schema. `scope.functions` and function checking targets bind the exact bytes;
functions do not appear in the blueprint's validators. The checker creates
`<id>` (CEK state) and `<id>_returns` (exact encoded return value) bindings.
Data function interfaces stay raw Data, and native interfaces use builtin values.
A function proposition must depend on its compiled program. Errors and exhausted
steps cannot satisfy a return-value predicate.

The Plutus `Example/Ual/Auction` example keeps annotations in `FormalSpec.hs`,
with imported bindings from `OnChain.hs`/`AuctionValidator.hs`. Its ledger model
and end-to-end runner live in CardanoLedgerApiBlaster:
`CardanoLedgerApi/Examples/Auction.lean` and
`Tests/BlueprintVerify/run_auction.py`. The runner checks concrete bid/payout
examples, quantified claims, and rejects altered helper code, wrong wire types,
invalid scopes and exhausted fuel. It writes separate evidence-bearing output.
Use a Z3 compatible with the loaded Blaster checkout; the environment manifest
pins the selected binary rather than assuming a globally installed version.

## Coordinated workspace command

Use sibling checkouts named `PlutusCoreBlaster`, `Lean-blaster` and
`CardanoLedgerApiBlaster`; the Plutus and CIPs locations are command arguments.
Both Lean consumers resolve the same `../Lean-blaster` directory. The tested
Blaster revision and toolchain versions are recorded in
`../../scripts/assurance-workspace.json`. In the Plutus build environment
(GHC 9.6.7, Cabal and its normal native dependencies), run from PlutusCoreBlaster:

```sh
python3 scripts/verify_assurance_workspace.py \
  --plutus /path/to/plutus --cips /path/to/CIPs \
  --z3 /path/to/compatible/z3 --output /path/to/results
```

Install the Python requirements in `CIP-XXXX/tests/requirements.txt` first.
`--ghc /path/to/ghc` selects a wrapped compiler. Machine-specific Cabal flags
belong in the ignored `cabal.assurance.project.local`, leaving the shared project
portable. `--ual /path/to/UniversalAnnotationLanguage` includes the specification
in source provenance. `--preflight-only` checks the
layout, pinned Blaster revision, compiler versions and the Z3 `recfun-finder`
capability. `--skip-build` is for an already-built workspace. No global PATH,
Git branch or toolchain configuration is changed. The solver's source baseline
is pinned in the lock file; each run additionally hashes the actual executable,
so another build cannot inherit old evidence merely by reporting the same version.

The command builds both Lean consumers, compiles all four Plutus generators,
regenerates and checks Game, Data/native parameters, Auction and recursive Tree,
and runs schema, encoding and negative regressions. Drivers share `runtime.py`,
which passes the same native library to Lean and the environment manifest.
`workspace-report.json` is written only after every required check passes and
records repository revisions, modified source hashes, binaries and results.

The `compiled-assurance` workflow checks out the current Core PR and exact sibling
revisions from the lock file, builds the pinned solver, enters Plutus’s GHC 9.6.7
Nix shell and runs this command. Its result bundle is uploaded even on failure.
The workflow must pass before release; adding the workflow is not itself evidence
that clean-checkout CI has passed. Update the dependency pins when companion PRs change.

## Recursive Data example

`example-ual-recursive` uses `deriveRecursiveDefinitions` to retain a finite
schema graph. It compiles a tree-sum validator and a tree-mirror helper; the latter's
code and argument/result references live in assurance only. The checker rejects
alias-only cycles, missing definitions and stale context snapshots. Recursive
arguments stay raw Data, preserving arbitrary finite values and malformed inputs.
The four symbolic claims cover specified tree shapes under a 3000-step bound;
they do not assert termination for every tree depth.

## Remaining implementation work

- Scott ABI support and compiler/profile conformance vectors.
- Establish ledger-valid fixtures for claims intended to cover real transactions.
- Run the coordinated suite in clean-checkout CI once the local changes are integrated.

Ledger-cost acceptance and helper-to-inlined-code equivalence remain separate
proof capabilities; the current profile does not claim either.

## Applied parameters

The parameter example checks two universal claims and four specialized-program
claims. Applied contexts include every ordered Flat term and a digest-bound
single-CBOR `appliedScript`. The checker validates each value's representation,
compares the specialized AST with the exact unoptimized template application,
and verifies its ledger script hash. Its wrapper exposes only runtime inputs.
Structural Data/native schemas are supported; unsupported refinements fail
explicitly. Nine negative cases cover missing coverage, order, artifact hashes,
wrong encodings, unrelated scripts, open terms and trailing bytes.
