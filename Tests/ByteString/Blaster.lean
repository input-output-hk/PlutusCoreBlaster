import Blaster
import PlutusCore.Bitwise
import PlutusCore.ByteString
import PlutusCore.Cbor
import PlutusCore.String
import PlutusCore.UPLC.BuiltinFunctions.Bitwise

/-! # Blaster on byte-level builtins of symbolic byte strings

The builtins below read or write single bytes. They used to go through `Char`, which Blaster
cannot translate on a symbolic string. They now go through `PlutusCore.Bytes`.

* `#smt_clean [goal]` checks that a goal translates to a well-formed query. This needs no solver, so it
  runs anywhere. The query is captured and searched for selectors of `String`, `Char`, `UInt32`,
  `BitVec` or `Fin`. Those appear when a character read escapes the seal, and Blaster still
  reports such a query as merely "Undetermined".
* Goals the optimizer settles on its own are run with `blaster` to the end; they need no solver
  either. The others need the solver that CI builds, so here they are only translated.

Goals that read bytes take `PlutusCore.Bytes.Spec` as a premise, since Blaster does not harvest
theorems. `PlutusCore.Bytes.spec` proves it. -/

namespace Tests.ByteString.Blaster

set_option warn.sorry false

open Lean Elab Command

/-- `#smt_clean [goal]` translates `goal` with the `blaster` tactic, without solving it, and fails
    unless a query was emitted and that query is free of the selectors an unsealed character read
    leaves behind. The tactic runs synchronously on a bare goal (unlike `#blaster`, which runs in a
    background task), so its output can be captured; no declaration is added. -/
elab "#smt_clean " "[" goal:term "]" : command => do
  let (out, _) ← IO.FS.withIsolatedStreams <| liftTermElabM do
    let ty ← Term.elabTerm goal (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mvar ← Meta.mkFreshExprMVar ty
    let tac ← `(tactic| blaster (only-smt-lib: 1) (dump-smt-lib: 1))
    discard <| Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
  unless (out.splitOn "Smt Query:").length > 1 do
    throwError "#smt_clean: no SMT query was emitted"
  -- `ByteString.mk.0` is a legitimate selector, hence the leading delimiter on `String.mk.`.
  for bad in [" String.mk.", "(String.mk.", "Char.", "UInt8", "UInt32", "BitVec", "Fin.mk"] do
    if (out.splitOn bad).length > 1 then
      throwError "#smt_clean: the SMT query mentions `{bad}`"

open PlutusCore.Bytes (Spec spec byteStr)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)
open PlutusCore.Bitwise (byteStringToInteger integerToByteString)
open PlutusCore.ByteString
  (appendByteString consByteStringV1 consByteStringV2 indexByteString lengthOfByteString
   sliceByteString)
open PlutusCore.String (encodeUtf8 decodeUtf8)
open PlutusCore.Cbor (encodeData)

/-! ## `Spec` holds, without axioms -/

/-- info: 'PlutusCore.Bytes.spec' does not depend on any axioms -/
#guard_msgs in #print axioms spec

/-! ## PR #71: `byteStringToInteger`, `integerToByteString`, `sliceByteString` -/

#smt_clean
  [Spec → ∀ (s : String), s.length = 2 → byteStringToInteger true s < 65536]

#smt_clean
  [Spec → ∀ (s : String), s.length = 1 → byteStringToInteger false s = byteStringToInteger true s]

#smt_clean
  [Spec → ∀ (s : String), s ≠ "\x01\x02" → byteStringToInteger true s ≠ 258]

#smt_clean
  [∀ (n : Integer) (s : String), integerToByteString true 2 n = .ok s → s.length = 2]

#smt_clean
  [Spec → ∀ (bs : ByteString) (s k : Integer), (sliceByteString s k bs).length ≤ bs.length]

/-! ## The other byte-level `ByteString` builtins: `indexByteString`, `consByteString` -/

#smt_clean
  [Spec → ∀ (bs : ByteString),
    indexByteString bs (lengthOfByteString bs) = .error "indexByteString: index out of bounds"]

#smt_clean
  [Spec → ∀ (bs : ByteString) (n : Integer), (consByteStringV1 n bs).length = bs.length + 1]

/-- `consByteString` (V2) prepends the table byte for an in-range `n`; the optimizer alone proves it. -/
example : ∀ (bs : ByteString) (n : Integer), 0 ≤ n → n ≤ 255 →
    consByteStringV2 n bs = .ok ⟨byteStr n.toNat ++ bs.data⟩ := by
  blaster

/-! ## PR #75: `encodeUtf8`, `decodeUtf8`, `serialiseData` -/

#smt_clean
  [Spec → ∀ (s : String), (encodeUtf8 s).length ≤ 4 * s.length]

#smt_clean
  [Spec → ∀ (s : String), s.length = 1 → decodeUtf8 (encodeUtf8 s) = .ok s]

#smt_clean
  [Spec → ∀ (bs : ByteString), bs.length = 0 → decodeUtf8 bs = .ok ""]

#smt_clean
  [Spec → ∀ (x : ByteString), x.length ≤ 23 →
    encodeData (.B x) = some (byteStr (64 + x.length) ++ x.data)]

#smt_clean
  [Spec → ∀ (x : ByteString) (i : Integer), encodeData (.List [.B x, .I i]) ≠ none]

/-- `serialiseData` succeeds on any byte string leaf; the optimizer alone proves it. -/
example : Spec → ∀ (x : ByteString), encodeData (.B x) ≠ none := by blaster

/-- `serialiseData` succeeds on any integer leaf; the optimizer alone proves it. -/
example : ∀ (i : Integer), encodeData (.I i) ≠ none := by blaster

/-! ## Byte reads mixed with the native string operations, and through the CEK builtin -/

#smt_clean
  [Spec → ∀ (a b : ByteString), a < b →
    byteStringToInteger true (appendByteString a b).data ≥ byteStringToInteger true a.data]

open PlutusCore.UPLC.CekValue (CekValue) in
open PlutusCore.UPLC.Term (Const) in
/-- The CEK-level builtin applied to a symbolic byte string; the optimizer alone proves it. -/
example : Spec → ∀ (bs : ByteString),
    PlutusCore.UPLC.BuiltinFunctions.Bitwise.byteStringToInteger
      [CekValue.VCon (Const.ByteString bs), CekValue.VCon (Const.Bool true)] ≠ none := by
  blaster

open PlutusCore.UPLC.CekValue (CekValue) in
open PlutusCore.UPLC.Term (Const) in
#smt_clean
  [Spec → ∀ (bs : ByteString) (n : Integer), bs.length = 1 →
    PlutusCore.UPLC.BuiltinFunctions.Bitwise.byteStringToInteger
      [CekValue.VCon (Const.ByteString bs), CekValue.VCon (Const.Bool true)] = some (CekValue.VCon (Const.Integer n)) →
    n < 256]

/-! ## Logical and bitwise builtins -/

section Bitwise
open PlutusCore.Bitwise
  (andByteString orByteString xorByteString complementByteString shiftByteString
   rotateByteString countSetBits findFirstSetBit readBit writeBits replicateByte)

#smt_clean
  [Spec → ∀ (a b : String), (andByteString false a b).length ≤ a.length]

#smt_clean
  [Spec → ∀ (a b : String), (orByteString true a b).length = Nat.max a.length b.length]

#smt_clean
  [Spec → ∀ (a : String), a.length = 1 → xorByteString false a a = "\x00"]

#smt_clean
  [Spec → ∀ (a : String), (complementByteString a).length = a.length]

#smt_clean
  [Spec → ∀ (a : String) (k : Integer), (shiftByteString a k).length = a.length]

#smt_clean
  [Spec → ∀ (a : String) (k : Integer), (rotateByteString a k).length = a.length]

#smt_clean
  [Spec → ∀ (a : String), countSetBits a ≤ 8 * (a.length : Integer)]

#smt_clean
  [Spec → ∀ (a : String), findFirstSetBit a < 8 * (a.length : Integer)]

#smt_clean
  [Spec → ∀ (a : String) (i : Integer), readBit a i = .ok true → countSetBits a > 0]

#smt_clean
  [Spec → ∀ (a b : String) (i : Integer), writeBits a [i] true = .ok b → readBit b i = .ok true]

#smt_clean
  [∀ (n : Integer) (s : String), replicateByte n 0 = .ok s → (s.length : Integer) = n]

open PlutusCore.UPLC.CekValue (CekValue) in
open PlutusCore.UPLC.Term (Const) in
/-- The CEK-level builtin applied to symbolic byte strings; the optimizer alone proves it. -/
example : Spec → ∀ (a b : ByteString),
    PlutusCore.UPLC.BuiltinFunctions.Bitwise.xorByteString
      [CekValue.VCon (Const.ByteString b), CekValue.VCon (Const.ByteString a), CekValue.VCon (Const.Bool false)]
    = some (CekValue.VCon (Const.ByteString ⟨xorByteString false a.data b.data⟩)) := by
  blaster

end Bitwise

/-! ## The check catches an unsealed read

With the seal lifted, the same kind of goal still yields a query, but one that names selectors of
the `Char` encoding that it never declares. -/

section Unsealed
attribute [local semireducible] PlutusCore.Bytes.instByteViewString

/-- error: #smt_clean: the SMT query mentions `(String.mk.` -/
#guard_msgs in
#smt_clean [∀ (s : String), s.length = 2 → byteStringToInteger true s < 65536]

end Unsealed

end Tests.ByteString.Blaster
