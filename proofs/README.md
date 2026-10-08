# Optional PlutusCore library facts

This package provides reusable Blaster summaries for Value lookup, insertion,
deletion, union, containment, Data encoding/decoding, and Data equality observers.
Import `PlutusCoreFacts`, or the narrower `PlutusCoreFacts.Value` and
`PlutusCoreFacts.Data` modules. The ordinary `PlutusCore` imports and default
package dependency are unchanged.

From the repository root:

```sh
cd proofs
lake build
lake test
```

Lean 4.24.0 and Z3 4.15.2 are used by CI. The package pins the supporting
[Lean-blaster fork](https://github.com/colll78/Lean-blaster/tree/7f7c0248d64a7f52547bf498104f5775cdfb9fbb),
which adds functional induction, explicit theorem summaries, and
`@[blaster_library]` registration. These extensions must be upstreamed or the
pin retained before this package can become a default upstream target.
The Value implementation is currently on the upstream `value-builtins` branch.
The ByteString `Std.Irrefl` instance is backported from upstream main so this
branch also supports current ledger consumers.

Theorems state sortedness, nonnegativity, and successful decoding/operation
premises where required. The tests exercise downstream summary use and reject
an insertion claim with its sortedness premise removed. Implementation helpers
are named under `PlutusCore.Value.Internal` to make their equations accessible
to this separate proof package; their bodies are unchanged.

The solver features are proposed in [Lean-blaster #285](https://github.com/input-output-hk/Lean-blaster/pull/285). The commit pin keeps this package buildable while that PR is pending.

## Trust boundary

These are SMT-verified facts. Blaster admits proved goals through the
`blasterProven` axiom rather than producing Lean kernel proof terms; solver
soundness and the Lean-to-SMT translation are therefore trusted. The library
attribute accepts only Blaster-proved theorems and restricts summary registration.
This package does not claim kernel verification of its SMT facts.
