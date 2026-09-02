import Blaster

import PlutusCore.Crypto.BLS12_381

/-!
  # Can `blaster` use the axioms of `Crypto/BLS12_381/Axioms.lean`?

  A tool-capability check, in the manner of `BlasterSmoke.lean`: nothing here is a
  statement about the curve. `BlasterSmoke` asks whether the BLS *types* encode into
  SMT-LIB; this file asks the next question -- whether the *axioms* about them ever reach
  the solver, and by which route.

  ## The mechanism

  `Blaster.Optimize.findLocalAxioms` (`Blaster/Optimize/Env.lean`) is the only thing that
  puts a standing fact into a query. It walks the environment and keeps a constant iff

  * `!Environment.isImportedConst env c` -- declared in **this module**, and
  * `isPropEnv info.type` -- the type is a `Prop`, so `axiom P : X → Prop` is skipped
    (its type is a `Type`), and
  * `!(← isTheorem c)` -- a local **theorem** is skipped.

  Three consequences, each measured below. Imported axioms are invisible (route A); a
  same-module `axiom` is picked up (route B, in `AxiomsBlasterHarvest.lean`); and a fact
  supplied as a *premise of the goal* reaches the solver like any other hypothesis
  (route C). Note what the third bullet rules out: an imported axiom cannot be laundered
  into a query by restating it as a local theorem, however trivial the proof.

  Route C is the one to use. It has the same solver power as route B (both are `Valid`
  below), and two advantages: the trust base stays honest -- the axiom is *used*, not
  duplicated, as `probe_reassoc`'s pinned footprint shows -- and it does not leak. A
  harvested axiom is prepended to *every* `blaster` call in its module, which is why
  route B needs a module of its own and why `ReclaimGlobalV2Bridge.lean` keeps its one
  assumption away from the twelve proved properties.

  Route C is also not new here: it is exactly the `VkDecodes` pattern of
  `ReclaimGlobalV2Properties.lean` -- a `def ... : Prop` bundling the needed facts, a
  `*_of (h : ...)` theorem proved by `blaster`, and a wrapper discharging `h`.

  ## Translatability: one wall left, and two that were removed

  Route C only moves a fact to the solver if the fact *translates*. Three groups of these
  axioms did not.

  **`GT`: fixed, by modelling it.** `axiom GT : Type` was an uninterpreted sort, which
  `translateNonOpaqueType` rejects outright, and that put every axiom mentioning the
  pairing target out of reach whatever the route. `Axioms.lean` now defines `GT` as ℤ/r --
  an element is its discrete log to base `gtGen`, reduced mod r -- so the sort is an
  ordinary one-field structure and `gtOne`/`gtGen`/`gtMul`/`gtPow` are ordinary `def`s.
  Blaster consequently discharges the whole ℤ/r layer with **no premise at all**:
  `gtPow_inj_mod`, `gtPow_emod`, `gtPow_add` and commutativity of `gtMul` are all `Valid`
  below, straight from the definitions. `probe_fv_pair_sound` is the payoff -- obligation 9
  of `ReclaimGlobalV2Bridge.lean`, previously "blocked behind 8".

  **The `InG1`/`InG2` guard: fixed, by making it `opaque`.** While
  `InG1 a := ∃ n : Int, a = n * g1` was a `def` it unfolded into the same curve arithmetic
  as the wall below, so *every* guarded axiom was unreachable however phrased -- the
  serialization axioms, and with them the `vkInSubgroup` seam, included. `Axioms.lean` now
  declares the two predicates `opaque`, with `InG1_def` as the only way in or out. An
  `opaque` translates to a `declare-fun` and its body is **not** unfolded, so the guard is
  now the uninterpreted predicate the axioms always treated it as. `probe_seam_of` and
  `probe_dlog_of` below are the payoff, over the real `Axioms.InG1` rather than a stand-in.

  The cost is one axiom per group. It is definitional -- the opaque body is the witness that
  a model exists -- and it must stay in `Axioms.lean`: its statement mentions `n * g1`, so as
  a *same-module* Prop axiom it would be harvested into every query in that module and
  hard-error goals that never mention `InG1`. (That is not hypothetical; it is what made the
  first attempt at this change appear to fail everywhere at once.)

  **G1/G2 arithmetic is a `partial def`: fixed, by sealing the instances.** `Axioms.lean`
  states its group laws over the `Cryptograph` `+`/`*`/`-`, which are computable and bottom
  out in `binaryInversion.loop`; `normConst` refuses partial functions, and that is still
  pinned as an expected error below -- *in this module*, which does not seal.

  The gate is reached while blaster unfolds a constant, so marking the four field-polymorphic
  `Cryptograph` `Point` instances `irreducible` stops the descent and leaves the operations
  uninterpreted, which is what a group law wants. `Tests/AxiomsBlasterSealed.lean` measures
  the before and after in one file and proves `sealed_group`, the first fact about G1
  arithmetic in this project that `blaster` established -- footprint: the three real axioms.
  It costs no restatement and no axiom, the only route past a wall here that is free.

  Sealing is a per-module opt-in and belongs in the consuming module, since it changes every
  later `blaster` call in its file -- which is why it is not done here, and why that file
  exists. Its limits are pinned there: a whole twelve-conjunct bundle is `Undetermined` where
  the two or three laws a goal needs are `Valid`, and the vacuity guards must stay
  `Undetermined` for any of it to mean anything.

  So the usable set is 18 of the 42 Prop axioms -- `Axioms.BlasterAlg` names them: `MlAlg`,
  `MlOkAlg`, `BridgeAlg`, and now `PairingAlg` (`e_dlog`, `e_nondegen`, `millerLoop_ok`) and
  `SerdeAlg` (all six). Two of those six never needed the fix:
  `g1_compress_uncompress`/`g2_compress_uncompress` carry no guard and mention only the
  `opaque` compress/uncompress builtins, so they translated all along -- an earlier revision
  of this header put all six behind the wall, which was wrong.

  ## The route not taken

  There is a second way past the same wall, kept here because it is what the validator layer
  will want. `PlutusCore` already has `opaque` wrappers for the builtins -- `opaque
  bls12_381_G1_add (x y) := x + y` -- and an `opaque` translates to a `declare-fun`, which is
  also the uninterpreted symbol a group law wants. `probe_g1_reassoc_of` below proves an
  associativity/commutativity consequence over `bls12_381_G1_add` by route C.

  Its cost is what makes it second choice: the `opaque` bodies are unreachable from proofs,
  so a restated law can be *stated* but not *discharged* without one definitional bridge
  axiom per operation (`bls12_381_G1_add x y = x + y`, …) -- measured to work, and the bridges
  would have to live in `G1.lean`/`G2.lean`, never in a `blaster` module. Sealing gets the
  same translatability for nothing, so the builtin restatement is worth doing only when a
  goal is *about* the builtins, which is where CEK-level obligations live.

  Note what neither route can be: a replacement. `OwnershipVerifyExample.lean` reasons about
  the `Cryptograph` operations directly, so those statements have to stay.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe

open PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G1.Internal (bls12_381_G1_add bls12_381_G1_uncompress)
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Pairing

/-! ## Route A -- imported axioms are invisible

    `mulMlResult_comm` and `mulMlResult_assoc` are imported and make the goal true; the
    solver never sees them. `Falsified` with a concrete counterexample, not
    `Undetermined`: `mulMlResult` arrives as an ordinary uninterpreted function, so Z3 is
    free to pick a non-commutative one. -/

#blaster (solve-result: 1) [∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x]

/-! ## Route C -- the same fact as a premise

    A genuine two-step derivation, so a `Valid` here is use rather than restatement:
    commutativity twice and associativity once. -/

/-- The two `MlResult` axioms as one premise, in the shape `VkDecodes` uses. -/
def MlAlg : Prop :=
  (∀ (a b   : BLS12_381_MlResult), a * b = b * a) ∧
  (∀ (a b c : BLS12_381_MlResult), (a * b) * c = a * (b * c))

set_option warn.sorry false in
theorem probe_reassoc_of (h : MlAlg) :
  ∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x := by blaster

/-- Discharged from the import -- the axioms are used, not duplicated. -/
theorem mlAlg : MlAlg := ⟨Axioms.mulMlResult_comm, Axioms.mulMlResult_assoc⟩

theorem probe_reassoc : ∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x :=
  probe_reassoc_of mlAlg

-- The point of route C: the footprint names the two real axioms and adds nothing. A
-- route-B proof of the same goal would carry a second, local copy of each.
/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe.probe_reassoc' depends on axioms: [Blaster.Tactic.blasterProven,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.mulMlResult_assoc,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.mulMlResult_comm]
-/
#guard_msgs in
#print axioms probe_reassoc

/-! ## Route C at the `MlOk` / `finalVerify` layer

    `MlOk` is `axiom MlOk : BLS12_381_MlResult → Prop`. Its type is not a `Prop`, so it
    is never harvested even in its own module; it translates as an uninterpreted
    predicate, which is all this needs. This is obligation 9's layer in
    `ReclaimGlobalV2Bridge.lean` -- and as far as that table can be pushed, since
    `finalVerify_sound` mentions `pi`. -/

#blaster [(∀ (m n : BLS12_381_MlResult),
             bls12_381_finalVerify m n = true → Axioms.MlOk m ∧ Axioms.MlOk n) →
          (∀ (m n : BLS12_381_MlResult), bls12_381_finalVerify m n = true → Axioms.MlOk m)]

/-! ## `GT` as ℤ/r -- the removed wall

    While `GT` was `axiom GT : Type` the goal below was a hard
    `translateNonOpaqueType: inductive info expected` and every pairing axiom was
    unreachable. Now the sort is a one-field structure and the operations are `def`s, so
    the ℤ/r layer needs no premise: these four are `Valid` from the definitions alone.

    The first is also the regression guard against the collapse trap that
    `BlasterSmoke`'s test 6 documents. `∀ (x : Axioms.GT), x = x` reports `Valid` whether
    or not `GT` translates, because the optimizer discharges it beforehand and encodes
    nothing -- it certified this capability falsely for as long as it was absent. A goal
    over `gtMul` cannot be collapsed that way. Note it is also `Valid` rather than
    `Falsified` now: under the model `gtMul` really is commutative, which is the group law
    the abstract phrasing deliberately withheld. -/

#blaster [∀ (x y : Axioms.GT), x * y = y * x]
#blaster [∀ (m n : Int), Axioms.gtGen ^ m = Axioms.gtGen ^ n ↔ m % Axioms.r = n % Axioms.r]
#blaster [∀ (m : Int), Axioms.gtGen ^ m = Axioms.gtGen ^ (m % Axioms.r)]
#blaster [∀ (m n : Int), Axioms.gtGen ^ (m + n) = Axioms.gtGen ^ m * Axioms.gtGen ^ n]

/-! ### The payoff -- obligation 9

    `finalVerify_millerLoop_pair_sound` is an existing corollary of `Axioms.lean` that no
    `blaster` goal could reach while `GT` was abstract. Two steps: `finalVerify_sound`,
    then `pi_millerLoop` on each side. Route C, discharged from the imports, so the
    footprint below is the honest one -- and note what is *not* in it: no `gt*` axiom,
    because there are none left. -/

def PairingBridge : Prop :=
  (∀ (m n : BLS12_381_MlResult), bls12_381_finalVerify m n = true → Axioms.pi m = Axioms.pi n) ∧
  (∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
     Axioms.pi (bls12_381_millerLoop p q) = Axioms.e p q)

set_option warn.sorry false in
theorem probe_fv_pair_sound_of (h : PairingBridge) :
  ∀ (p₁ p₂ : BLS12_381_G1_Element) (q₁ q₂ : BLS12_381_G2_Element),
    bls12_381_finalVerify (bls12_381_millerLoop p₁ q₁) (bls12_381_millerLoop p₂ q₂) = true →
    Axioms.e p₁ q₁ = Axioms.e p₂ q₂ := by blaster

theorem pairingBridge : PairingBridge :=
  ⟨Axioms.finalVerify_sound, fun p q => Axioms.pi_millerLoop p q⟩

theorem probe_fv_pair_sound :
  ∀ (p₁ p₂ : BLS12_381_G1_Element) (q₁ q₂ : BLS12_381_G2_Element),
    bls12_381_finalVerify (bls12_381_millerLoop p₁ q₁) (bls12_381_millerLoop p₂ q₂) = true →
    Axioms.e p₁ q₁ = Axioms.e p₂ q₂ := probe_fv_pair_sound_of pairingBridge

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe.probe_fv_pair_sound' depends on axioms: [propext,
 Quot.sound,
 Blaster.Tactic.blasterProven,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.finalVerify_sound,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi_millerLoop]
-/
#guard_msgs in
#print axioms probe_fv_pair_sound

/-! ## The remaining wall -- the `Cryptograph` group operations do not translate

    `g1_add_comm` as stated, with no `InG1` guard in sight: the `+` alone is enough, which
    is why the guard going `opaque` did nothing for `G1Alg`/`G2Alg`. Adding a guard to this
    goal no longer changes the outcome either way -- the conclusion is what fails. -/

/--
error: normConst: partial function not supported Cryptograph.BLS12_381.Internal.binaryInversion.loop !!!
-/
#guard_msgs in
#blaster [∀ (a b : BLS12_381_G1_Element), a + b = b + a]

/-! ## Past the remaining wall -- the same laws over the `opaque` builtins

    `bls12_381_G1_add` is `opaque`, so it becomes a `declare-fun` and the group law
    becomes usable. First that the goal is not true for free -- congruence gives nothing --
    and then the same goal under premises. -/

#blaster (solve-result: 1) [∀ (p q : BLS12_381_G1_Element),
  bls12_381_G1_add p q = bls12_381_G1_add q p]

/-- Commutativity and associativity over the opaque builtin, as one premise. -/
def G1AddAlg : Prop :=
  (∀ (a b : BLS12_381_G1_Element), bls12_381_G1_add a b = bls12_381_G1_add b a) ∧
  (∀ (a b c : BLS12_381_G1_Element),
     bls12_381_G1_add (bls12_381_G1_add a b) c = bls12_381_G1_add a (bls12_381_G1_add b c))

set_option warn.sorry false in
/-- Not discharged: `Axioms.g1_add_comm` is stated over the `Cryptograph` `+`, and
    `bls12_381_G1_add`'s `opaque` body is not accessible, so there is no term of
    `G1AddAlg` to supply. Proving this goal is the capability under test; obtaining the
    premise is the restatement the header describes. -/
theorem probe_g1_reassoc_of (h : G1AddAlg) :
  ∀ (p q r : BLS12_381_G1_Element),
    bls12_381_G1_add (bls12_381_G1_add p q) r = bls12_381_G1_add (bls12_381_G1_add r q) p := by
      blaster

/-! ## Past the guard -- the `vkInSubgroup` seam, with the real predicate

    `ReclaimGlobalV2Properties.lean` proves the nine `vk*_ok` decoding facts and notes
    that composing them with `g1_uncompress_subgroup` "*is* `vkInSubgroup` for this key".
    That composition could not happen inside `blaster` while `InG1` was a `def`. Now that it
    is `opaque` the goal below is over `Axioms.InG1` itself -- no stand-in predicate, and the
    conclusion is a fact about the real subgroup rather than about an uninterpreted symbol
    that resembles it.

    Two steps: `g1_uncompress_subgroup` for the guard, then `g1_uncompress_compress` under
    it. `SerdeAlg` rather than `BlasterAlg`, to keep the footprint to what the goal uses. -/

set_option warn.sorry false in
theorem probe_seam_of (h : Axioms.SerdeAlg) :
  ∀ (b : ByteString) (p : BLS12_381_G1_Element),
    bls12_381_G1_uncompress b = Except.ok p →
    Axioms.InG1 p ∧ bls12_381_G1_uncompress (bls12_381_G1_compress p) = Except.ok p := by
      blaster

theorem probe_seam :
  ∀ (b : ByteString) (p : BLS12_381_G1_Element),
    bls12_381_G1_uncompress b = Except.ok p →
    Axioms.InG1 p ∧ bls12_381_G1_uncompress (bls12_381_G1_compress p) = Except.ok p :=
  probe_seam_of Axioms.serdeAlg

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe.probe_seam' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blaster.Tactic.blasterProven,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_compress_uncompress,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_uncompress_compress,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_uncompress_subgroup,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_compress_uncompress,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_uncompress_compress,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_uncompress_subgroup]
-/
#guard_msgs in
#print axioms probe_seam

/-! ## Past the guard -- the pairing layer

    `e_dlog` twice over, with the ℤ/r layer closing the gap: `g2_dlog q = g2_dlog q'` makes
    the two exponents equal, and `gtPow` is a `def`, so the solver finishes without any
    `gt*` premise. Unreachable at any phrasing while the guard unfolded. -/

set_option warn.sorry false in
theorem probe_dlog_of (h : Axioms.PairingAlg) :
  ∀ (p : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
    Axioms.InG1 p → Axioms.InG2 q → Axioms.InG2 q' →
    Axioms.g2_dlog q = Axioms.g2_dlog q' → Axioms.e p q = Axioms.e p q' := by blaster

/-! `millerLoop_ok` -- the third `PairingAlg` conjunct -- composed with `MlOkAlg`. Both
    guards are uninterpreted; `bls12_381_millerLoop` is `opaque` and `MlOk` an
    `axiom _ : _ → Prop`. -/

set_option warn.sorry false in
theorem probe_miller_ok_of (h : Axioms.PairingAlg) (h2 : Axioms.MlOkAlg) :
  ∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.MlOk (bls12_381_millerLoop p q * bls12_381_millerLoop p q) := by blaster

/-! ## `DlogFacts` -- derived facts, passed because the solver cannot re-derive them

    `Axioms.DlogFacts` is not axioms: every conjunct is a theorem of `Axioms.lean`. It is
    bundled for route C all the same, because `g1_dlog` is uninterpreted and the `∃` that
    would tie it to the generator is behind `InG1_def`, so no query can reconstruct any of
    it.

    Two steps here, and a statement worth having: equal dlog products make the *on-chain*
    check pass. `e_eq_iff_dlog` turns the arithmetic premise into a pairing equality,
    `finalVerify_millerLoop_pair` turns that into `finalVerify ... = true`. -/

set_option warn.sorry false in
theorem probe_dlog_finalVerify_of (h : Axioms.DlogFacts) :
  ∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.InG1 p' → p' ≠ 0 → Axioms.InG2 q' → q' ≠ 0 →
    (Axioms.g1_dlog p * Axioms.g2_dlog q) % Axioms.r
      = (Axioms.g1_dlog p' * Axioms.g2_dlog q') % Axioms.r →
    bls12_381_finalVerify (bls12_381_millerLoop p q) (bls12_381_millerLoop p' q') = true := by
      blaster

theorem probe_dlog_finalVerify :
  ∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.InG1 p' → p' ≠ 0 → Axioms.InG2 q' → q' ≠ 0 →
    (Axioms.g1_dlog p * Axioms.g2_dlog q) % Axioms.r
      = (Axioms.g1_dlog p' * Axioms.g2_dlog q') % Axioms.r →
    bls12_381_finalVerify (bls12_381_millerLoop p q) (bls12_381_millerLoop p' q') = true :=
  probe_dlog_finalVerify_of Axioms.dlogFacts

/-! The footprint is the honest accounting of what a derived premise costs. No *new* axiom
    appears -- `DlogFacts` is theorems -- but the proofs behind those theorems run through
    `g1_cyclic`, so the G1/G2 scalar-action axioms and `InG1_def` are named here even though
    the goal mentions no point operation at all. "Free" means free of new assumptions, not
    free in the audit. -/

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe.probe_dlog_finalVerify' depends on axioms: [propext,
 Quot.sound,
 Blaster.Tactic.blasterProven,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.InG1_def,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.InG2_def,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.MlOk,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.finalVerify_complete,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.finalVerify_sound,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_dlog_scalarMul,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_mod,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_one,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_zero,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_dlog_scalarMul,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_mod,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_one,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_zero,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.millerLoop_ok,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi_millerLoop]
-/
#guard_msgs in
#print axioms probe_dlog_finalVerify

/-! `g1_dlog_emod_eq_zero_iff` twice over: two subgroup points whose dlogs vanish mod r are
    the same point, both being zero. The kind of step `acceptedPubUnique` takes by hand. -/

set_option warn.sorry false in
theorem probe_dlog_zero_of (h : Axioms.DlogFacts) :
  ∀ (p p' : BLS12_381_G1_Element),
    Axioms.InG1 p → Axioms.InG1 p' →
    Axioms.g1_dlog p % Axioms.r = 0 → Axioms.g1_dlog p' % Axioms.r = 0 → p = p' := by blaster

end PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe
