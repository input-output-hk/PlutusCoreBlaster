import Blaster

import PlutusCore.Crypto.BLS12_381

/-!
  # Route B: a same-module `axiom` is harvested

  The other half of `AxiomsBlasterProbe.lean`, which measures routes A and C and
  documents the mechanism. Split off for the reason the split demonstrates:
  `findLocalAxioms` prepends every Prop-typed same-module axiom to *every* `blaster` call
  in the module, so the axiom below would silently turn that file's route-A test --
  which must come back `Falsified` -- into `Valid`, and the walls it pins would be pinned
  under different hypotheses.

  That leak is the argument for route C, and the reason `ReclaimGlobalV2Bridge.lean`
  keeps `artifactImplementsVerifyDestination` out of `ReclaimGlobalV2Properties.lean`.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterHarvest

open PlutusCore.Crypto.BLS12_381.Pairing

/-! ## Harvesting without retyping the statements

    `findLocalAxioms` matches on the constant *kind* -- its `filterMapM` keeps `.axiomInfo`
    and returns `none` for everything else -- so an imported axiom cannot be brought into a
    query by any local declaration that is not itself an `axiom`. Neither
    `def loc := Axioms.mulMlResult_comm` nor a `theorem` restating it counts, whatever its
    proof, and `export`/`open` do not help either: `isImportedConst` is per-constant
    provenance, fixed where the constant is declared, not name resolution.

    What *can* be avoided is writing the statements twice. `Axioms.MlAlg` is the pair as
    one closed `Prop`, stated in `Axioms.lean` beside the two axioms, so the harvested
    copy below is one line with no mathematics in it. -/

axiom mlAlgLocal : Axioms.MlAlg

/-- The copy is logically free: the imports already prove it. Route B duplicates the trust
    base where route C uses it, and this is what keeps the duplicate honest -- a copy that
    could not be discharged would be a new assumption, not a harvested one. -/
theorem mlAlgLocal_redundant : Axioms.MlAlg := Axioms.mlAlg

-- The goal `AxiomsBlasterProbe`'s route-A test reports `Falsified` on, verbatim. The
-- only difference is the module it sits in.
#blaster [∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x]

/-! ## The cost route C does not pay

    The tactic assigns `blasterProven <goal>` (`Blaster/Command/Tactic.lean`), so the proof
    term never mentions a harvested axiom: the footprint of `reassoc` is
    `blasterProven` alone, and `mlAlgLocal` is nowhere in it. Route B does not merely
    duplicate the trust base, it leaves the duplicate *unrecorded* -- the only trace is
    `mlAlgLocal_redundant`, whose footprint names the two real axioms. Contrast
    `probe_reassoc`, which proves the same goal by route C and reports them directly. -/

set_option warn.sorry false in
theorem reassoc : ∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x := by blaster

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterHarvest.reassoc' depends on axioms: [Blaster.Tactic.blasterProven]
-/
#guard_msgs in
#print axioms reassoc

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterHarvest.mlAlgLocal_redundant' depends on axioms: [PlutusCore.Crypto.BLS12_381.Axioms.Internal.mulMlResult_assoc,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.mulMlResult_comm]
-/
#guard_msgs in
#print axioms mlAlgLocal_redundant

end PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterHarvest
