import Blaster
import PlutusCore.Bitwise
import PlutusCore.ByteString
import PlutusCore.Cbor
import PlutusCore.String
import PlutusCore.UPLC.BuiltinFunctions.Bitwise

/-! # Blaster on byte-level builtins of symbolic byte strings

The builtins below read or write single bytes. They used to go through `Char`, which Blaster
cannot translate on a symbolic string. They now go through `PlutusCore.Bytes`.

* `#smt_clean [goal]` checks that a goal translates to a well-formed query, without solving it.
  The query is captured and searched for selectors of `String`, `Char`, `UInt32`, `BitVec` or
  `Fin`. Those appear when a character read escapes the seal, and Blaster still reports such a
  query as merely "Undetermined". Then z3 parses the query's declarations and assertions, which any
  z3 can do; it rejects a malformed datatype declaration, which Blaster can emit (see
  `PlutusCore.Bytes.Cell`). Without z3, the parse is skipped with a warning.
* Goals the optimizer settles on its own are run with `blaster` to the end; they need no solver
  either. The others need the solver that CI builds, so here they are only translated.
* The goals in "`Spec` is enough" read bytes back, or work on literals. Each is also proved in
  Lean, and `Tests.ByteString.SymbolicReads` proves it with the solver.

Goals that read bytes take `PlutusCore.Bytes.Spec` as a premise, since Blaster does not harvest
theorems. `PlutusCore.Bytes.spec` proves it. -/

namespace Tests.ByteString.Blaster

set_option warn.sorry false

open Lean Elab Command

/-- Whether z3 accepts the declarations and assertions of `query`, without solving it: the
    `set-option` and `set-simplifier` lines are left out, so that any z3 can parse the rest. Returns
    z3's first error, or `none`. Returns `none` too when z3 cannot be run, with a warning. -/
def z3Rejects (query : String) : CommandElabM (Option String) := do
  let body := query.splitOn "\n" |>.filter (fun l =>
    !(l.startsWith "(set-option") && !(l.startsWith "(set-simplifier"))
  let input := "\n".intercalate body ++ "\n(exit)\n"
  try
    let child ← IO.Process.spawn
      { cmd := "z3", args := #["-in"], stdin := .piped, stdout := .piped, stderr := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.putStr input
    stdin.flush
    let stdout ← IO.asTask child.stdout.readToEnd
    discard <| child.wait
    let out ← IO.ofExcept stdout.get
    return out.splitOn "\n" |>.find? (·.startsWith "(error")
  catch e =>
    logWarning m!"#smt_clean: could not run z3 to parse the query ({e.toMessageData})"
    return none

/-- `#smt_clean [goal]` translates `goal` with the `blaster` tactic, without solving it, and fails
    unless a query was emitted, that query is free of the selectors an unsealed character read
    leaves behind, and z3 accepts its declarations (Blaster can emit a datatype declaration that
    z3 rejects; see `PlutusCore.Bytes.Cell`). The tactic runs synchronously on a bare goal (unlike
    `#blaster`, which runs in a background task), so its output can be captured; no declaration is
    added. -/
elab "#smt_clean " "[" goal:term "]" : command => do
  let (out, _) ← IO.FS.withIsolatedStreams <| liftTermElabM do
    let ty ← Term.elabTerm goal (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mvar ← Meta.mkFreshExprMVar ty
    let tac ← `(tactic| blaster (only-smt-lib: 1) (dump-smt-lib: 1))
    discard <| Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
  let some query := (out.splitOn "Smt Query:")[1]?
    | throwError "#smt_clean: no SMT query was emitted"
  -- `ByteString.mk.0` is a legitimate selector, hence the leading delimiter on `String.mk.`.
  for bad in [" String.mk.", "(String.mk.", "Char.", "UInt8", "UInt32", "BitVec", "Fin.mk"] do
    if (out.splitOn bad).length > 1 then
      throwError "#smt_clean: the SMT query mentions `{bad}`"
  if let some err ← z3Rejects query then
    throwError "#smt_clean: z3 rejects the SMT query: {err}"

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
  [Spec → ∀ (a b : Nat), a < 256 → b < 256 → byteStringToInteger true (byteStr a ++ byteStr b) < 65536]

#smt_clean
  [Spec → ∀ (s : String), s.length = 1 → byteStringToInteger false s = byteStringToInteger true s]

-- Reading the bytes back needs the last conjunct of `Spec`, which fixes what `uncons` returns.
#smt_clean
  [Spec → ∀ (a b : Nat), a < 256 → b < 256 →
    byteStringToInteger true (byteStr a ++ byteStr b) = 258 → a = 1 ∧ b = 2]

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
  [Spec → ∀ (a : Nat) (n : Integer), a < 256 →
    PlutusCore.UPLC.BuiltinFunctions.Bitwise.byteStringToInteger
      [CekValue.VCon (Const.ByteString ⟨byteStr a⟩), CekValue.VCon (Const.Bool true)] = some (CekValue.VCon (Const.Integer n)) →
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

/-! ## `Spec` is enough

Every goal here holds only because of what `Spec` says about the sealed primitives. Each is
translated here and proved in Lean; `Tests.ByteString.SymbolicReads` proves it with the solver.

The goals on symbolic byte strings read bytes back. Their Lean proofs use only the premise
`h : Spec` (through `Spec.uncons_byteStr_append` and the other accessors) and never open the seal,
so they fail if `Spec` leaves open the code that `uncons` returns. The last two goals work on
literals, through `Spec`'s table of byte values. -/

section SpecIsEnough
open PlutusCore.Bytes (uncons dropB)
open PlutusCore.Bitwise (readBit)
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Const)

/-- The first byte of a byte string that starts with `k` is `k`. -/
def indexCons : Prop :=
  Spec → ∀ (k : Nat) (bs : ByteString), k < 256 → indexByteString ⟨byteStr k ++ bs.data⟩ 0 = .ok k

#smt_clean [indexCons]

theorem indexCons_holds : indexCons := by
  intro h k bs hk
  unfold indexByteString
  rw [if_neg (by decide)]
  show (match uncons (byteStr k ++ bs.data) with
        | none => throw "indexByteString: index out of bounds"
        | some ⟨b, _⟩ => pure (b : Integer)) = _
  rw [h.uncons_byteStr_append k bs.data hk]
  rfl

/-- `consByteString` then `indexByteString` gives the byte back. -/
def consIndex : Prop :=
  Spec → ∀ (n : Integer) (bs r : ByteString), consByteStringV2 n bs = .ok r →
    indexByteString r 0 = .ok n

#smt_clean [consIndex]

theorem consIndex_holds : consIndex := by
  intro h n bs r hr
  unfold consByteStringV2 at hr
  split at hr
  · next hn =>
    cases hr
    have h0 : (0 : Int) ≤ n ∧ (n : Int) ≤ 255 := by
      revert hn; simp only [Integer, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hn' : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg h0.1
    have hlt : n.toNat < 256 := by
      apply Int.ofNat_lt.mp
      rw [hn']
      exact Int.lt_of_le_of_lt h0.2 (by decide)
    rw [indexCons_holds h n.toNat bs hlt]
    exact congrArg Except.ok hn'
  · cases hr

/-- Two bytes convert to the number they spell. -/
def bstoiTwo : Prop :=
  Spec → ∀ (a b : Nat), a < 256 → b < 256 →
    byteStringToInteger true (byteStr a ++ byteStr b) = .ofNat (256 * a + b)

#smt_clean [bstoiTwo]

theorem bstoiTwo_holds : bstoiTwo := by
  intro h a b ha hb
  have hlen : (byteStr a ++ byteStr b).length = 2 := by
    rw [String.length_append, h.byteStr_length a ha, h.byteStr_length b hb]
  unfold byteStringToInteger
  rw [if_pos rfl, hlen]
  show Int.ofNat (match uncons (byteStr a ++ byteStr b) with
    | none => 0
    | some ⟨x, t⟩ => PlutusCore.Bitwise.BitwiseInternal.bstoi_be_loop 1 t (0 * 256 + x)) = _
  rw [h.uncons_byteStr_append a (byteStr b) ha]
  show Int.ofNat (match uncons (byteStr b) with
    | none => 0 * 256 + a
    | some ⟨x, t⟩ => PlutusCore.Bitwise.BitwiseInternal.bstoi_be_loop 0 t ((0 * 256 + a) * 256 + x)) = _
  rw [h.uncons_byteStr b hb]
  show Int.ofNat ((0 * 256 + a) * 256 + b) = _
  congr 1; omega

/-- The same through the CEK machine's `ByteStringToInteger` dispatch, which reaches the byte loop. -/
def bstoiTwoCek : Prop :=
  Spec → ∀ (a b : Nat), a < 256 → b < 256 →
    PlutusCore.UPLC.BuiltinFunctions.Bitwise.byteStringToInteger
      [CekValue.VCon (Const.ByteString ⟨byteStr a ++ byteStr b⟩), CekValue.VCon (Const.Bool true)]
    = some (CekValue.VCon (Const.Integer (.ofNat (256 * a + b))))

#smt_clean [bstoiTwoCek]

theorem bstoiTwoCek_holds : bstoiTwoCek := by
  intro h a b ha hb
  show some (CekValue.VCon (Const.Integer (byteStringToInteger true (byteStr a ++ byteStr b)))) = _
  rw [bstoiTwo_holds h a b ha hb]

/-- Bit 0 of a one-byte string is the low bit of the byte. -/
def readBitOne : Prop :=
  Spec → ∀ (x : Nat), x < 256 → readBit (byteStr x) 0 = .ok (x % 2 = 1)

#smt_clean [readBitOne]

theorem readBitOne_holds : readBitOne := by
  intro h x hx
  unfold readBit
  show (if 8 * (byteStr x).length ≤ 0 then throw "readBit: index out of bounds"
    else match uncons (dropB ((byteStr x).length - 0 / 8 - 1) (byteStr x)) with
      | none => pure false
      | some ⟨y, _⟩ => pure (decide (PlutusCore.Bitwise.BitwiseInternal.bitAt (y % 256) (0 % 8) = 1))) = _
  rw [h.byteStr_length x hx, if_neg (by decide)]
  show (match uncons (byteStr x) with
    | none => pure false
    | some ⟨y, _⟩ => pure (decide (PlutusCore.Bitwise.BitwiseInternal.bitAt (y % 256) 0 = 1))) = _
  rw [h.uncons_byteStr x hx]
  show Except.ok (decide (x % 256 % 2 = 1)) = _
  rw [Nat.mod_eq_of_lt hx]

/-- Index 1 of a literal byte string. The seal stops Blaster from evaluating it; the solver works it
    out from `Spec`'s table of byte values. -/
def literalIndex : Prop :=
  Spec → indexByteString ⟨"\x05\x07"⟩ 1 = .ok 7

#smt_clean [literalIndex]

theorem literalIndex_holds : literalIndex := fun _ => by with_unfolding_all rfl

/-- `serialiseData` of a literal list, compared with its bytes. The optimizer alone proves it, by
    substituting the byte values from `Spec`'s table, so no solver is needed. -/
theorem literalSerialise :
    Spec → encodeData (.List [.I 1, .B ⟨"\x01\x02"⟩]) = some "\x9f\x01\x42\x01\x02\xff" := by
  blaster

end SpecIsEnough

/-! ## The check catches an unsealed read

With the seal lifted, the same kind of goal still yields a query, but one that names selectors of
the `Char` encoding that it never declares. -/

section Unsealed
attribute [local semireducible] PlutusCore.Bytes.instByteViewString

/-- error: #smt_clean: the SMT query mentions `(String.mk.` -/
#guard_msgs in
#smt_clean
  [∀ (a b : Nat), a < 256 → b < 256 → byteStringToInteger true (byteStr a ++ byteStr b) < 65536]

end Unsealed

/-! ## The check catches a query that z3 rejects

Blaster (at the pinned commit) gives `Prod` and `Except` each other's parameter names when both are
in one query, and z3 rejects the declaration. This is why `PlutusCore.Bytes.uncons` returns a
`Cell` rather than a pair. If a Blaster update fixes it, this check fails and can go. -/

section Rejected
opaque pairOf : Nat → Option (Nat × String)
opaque exceptOf : Nat → Except String Nat
def pairCode (n : Nat) : Nat := match pairOf n with | some p => p.1 | none => 0
def exceptValue (n : Nat) : Nat := match exceptOf n with | .ok x => x | .error _ => 0

/--
error: #smt_clean: z3 rejects the SMT query: (error "line 20 column 18: invalid datatype declaration, unknown sort '@ε'")
-/
#guard_msgs in
#smt_clean [∀ n, pairCode n = 0 → exceptValue n = 0]
end Rejected

end Tests.ByteString.Blaster
