# Aiken spending fixture

This directory keeps the independent compiler input for the complete-program
optimization test. `validators/eager_beneficiary.ak` validates every signer's
28-byte length before checking beneficiary membership. This eager traversal is
deliberate; the minimal Aiken `list.has` validator does not perform it.

The tracked `eager_beneficiary.uplc` was produced with Aiken v1.1.24 and
stdlib v3.0.0. `compiler.json` identifies the compiler release and
`provenance.json` records the compiled file's SHA-256. From this directory,
run `aiken build --uplc` to regenerate the readable UPLC artifact.

`Tests/UPLC/Optimize/AikenFixture.lean` contains the Lean representation used
by the full-program test in `Tests/UPLC/Optimize/Generic.lean`. That test checks
that both supported loop skeletons occur in the fixture and that the generic
extension prepares the complete program with a bounded residual. The fixture
fixes the surrounding context shape while leaving raw signatory elements
symbolic. These synthetic contexts are shape tests, not ledger-valid
transactions.

The historical fixture-specific optimization and its measurements live in the
original experiment commit `77d7fa2`; they are not required by the generic
extension.
