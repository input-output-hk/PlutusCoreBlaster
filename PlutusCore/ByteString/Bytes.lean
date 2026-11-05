/-! # Byte-level access to `String`-carried byte strings, in a form Blaster can translate

`ByteString` and the Plutus `string` type are both carried by a Lean `String`. Blaster maps
`String` to the SMT string sort, where `++`, `String.length`, `=`, `<`, `≤` and string literals
are native. Anything that reaches a `Char` (`String.data`, `Char.ofNat`, `Char.toNat`, `UInt8`)
unfolds to `UInt32`, `BitVec` and `Fin`, which Blaster cannot translate for a symbolic string.

The builtins that touch individual bytes therefore go through this module only:

* **Writers** build bytes with `byteStr k`, the one-byte string with code `k < 256`, looked up in
  a list of 256 string literals; no `Char` is involved.
* **Readers** take strings apart with `uncons` and rebuild characters with `cpStr`. These two are
  the only primitives that look at characters. Their single instance, `instByteViewString`, is
  `@[irreducible]`, which Blaster treats as a seal: both become uninterpreted functions. Every
  reader is ordinary recursion over them (`takeB`, `dropB` and the builtins), so Blaster still
  sees the real algorithm.

`Spec` states what a solver needs to know about the sealed pair, and `spec` proves it without
axioms. Blaster does not pick up theorems, so a goal that reads bytes from a symbolic string takes
`Spec` as a premise:

```
#blaster [PlutusCore.Bytes.Spec → ∀ (s : String), (sliceByteString 0 2 ⟨s⟩).length ≤ 2]
```

The seal costs two things.
* Blaster no longer evaluates a reader applied to a literal; the solver has to work it out from
  `Spec`. A module that only needs concrete evaluation can lift the seal with
  `attribute [local semireducible] PlutusCore.Bytes.instByteViewString`.
* `rfl` and `decide` stop at the seal too. `with_unfolding_all rfl`, `decide +kernel`,
  `native_decide`, `#eval` and `#guard` all still evaluate readers.
-/

namespace PlutusCore.Bytes

/-- `byteTable[k]` is the one-character string with code `k`, for `k < 256`.

    It is a list of literals on purpose. A 256-arm `match` runs out of heartbeats when elaborated,
    and a 256-leaf `if` tree makes Blaster's optimizer hang on goals that call it a few times. -/
def byteTable : List String := [
  "\x00", "\x01", "\x02", "\x03", "\x04", "\x05", "\x06", "\x07", "\x08", "\x09", "\x0a", "\x0b", "\x0c", "\x0d", "\x0e", "\x0f",
  "\x10", "\x11", "\x12", "\x13", "\x14", "\x15", "\x16", "\x17", "\x18", "\x19", "\x1a", "\x1b", "\x1c", "\x1d", "\x1e", "\x1f",
  "\x20", "\x21", "\x22", "\x23", "\x24", "\x25", "\x26", "\x27", "\x28", "\x29", "\x2a", "\x2b", "\x2c", "\x2d", "\x2e", "\x2f",
  "\x30", "\x31", "\x32", "\x33", "\x34", "\x35", "\x36", "\x37", "\x38", "\x39", "\x3a", "\x3b", "\x3c", "\x3d", "\x3e", "\x3f",
  "\x40", "\x41", "\x42", "\x43", "\x44", "\x45", "\x46", "\x47", "\x48", "\x49", "\x4a", "\x4b", "\x4c", "\x4d", "\x4e", "\x4f",
  "\x50", "\x51", "\x52", "\x53", "\x54", "\x55", "\x56", "\x57", "\x58", "\x59", "\x5a", "\x5b", "\x5c", "\x5d", "\x5e", "\x5f",
  "\x60", "\x61", "\x62", "\x63", "\x64", "\x65", "\x66", "\x67", "\x68", "\x69", "\x6a", "\x6b", "\x6c", "\x6d", "\x6e", "\x6f",
  "\x70", "\x71", "\x72", "\x73", "\x74", "\x75", "\x76", "\x77", "\x78", "\x79", "\x7a", "\x7b", "\x7c", "\x7d", "\x7e", "\x7f",
  "\x80", "\x81", "\x82", "\x83", "\x84", "\x85", "\x86", "\x87", "\x88", "\x89", "\x8a", "\x8b", "\x8c", "\x8d", "\x8e", "\x8f",
  "\x90", "\x91", "\x92", "\x93", "\x94", "\x95", "\x96", "\x97", "\x98", "\x99", "\x9a", "\x9b", "\x9c", "\x9d", "\x9e", "\x9f",
  "\xa0", "\xa1", "\xa2", "\xa3", "\xa4", "\xa5", "\xa6", "\xa7", "\xa8", "\xa9", "\xaa", "\xab", "\xac", "\xad", "\xae", "\xaf",
  "\xb0", "\xb1", "\xb2", "\xb3", "\xb4", "\xb5", "\xb6", "\xb7", "\xb8", "\xb9", "\xba", "\xbb", "\xbc", "\xbd", "\xbe", "\xbf",
  "\xc0", "\xc1", "\xc2", "\xc3", "\xc4", "\xc5", "\xc6", "\xc7", "\xc8", "\xc9", "\xca", "\xcb", "\xcc", "\xcd", "\xce", "\xcf",
  "\xd0", "\xd1", "\xd2", "\xd3", "\xd4", "\xd5", "\xd6", "\xd7", "\xd8", "\xd9", "\xda", "\xdb", "\xdc", "\xdd", "\xde", "\xdf",
  "\xe0", "\xe1", "\xe2", "\xe3", "\xe4", "\xe5", "\xe6", "\xe7", "\xe8", "\xe9", "\xea", "\xeb", "\xec", "\xed", "\xee", "\xef",
  "\xf0", "\xf1", "\xf2", "\xf3", "\xf4", "\xf5", "\xf6", "\xf7", "\xf8", "\xf9", "\xfa", "\xfb", "\xfc", "\xfd", "\xfe", "\xff"
]

/-- The one-byte string with code `k`, for `k < 256` (`""` otherwise). -/
def byteStr (k : Nat) : String := byteTable.getD k ""

/-- The character-level view of a string. The class exists only so that its one instance can be
    sealed: Blaster honours `@[irreducible]` on an instance, but not on a plain `def`. -/
class ByteView (α : Type) where
  /-- The code of the first character and the rest, or `none` for the empty string. -/
  uncons : α → Option (Nat × α)
  /-- The one-character string with the given code. -/
  cpStr  : Nat → α

/-- The sealed instance. The kernel still unfolds it, so everything about it stays provable. -/
@[irreducible] instance instByteViewString : ByteView String where
  uncons s := match s.data with
    | [] => none
    | c :: cs => some (c.toNat, ⟨cs⟩)
  cpStr c := String.singleton (Char.ofNat c)

export ByteView (uncons cpStr)

/-- The first `n` characters of `s` (all of `s` when it is shorter). -/
def takeB : Nat → String → String
  | 0, _ => ""
  | n + 1, s =>
    match uncons s with
    | none => ""
    | some (b, t) => cpStr b ++ takeB n t

/-- `s` without its first `n` characters (`""` when it is shorter). -/
def dropB : Nat → String → String
  | 0, s => s
  | n + 1, s =>
    match uncons s with
    | none => ""
    | some (_, t) => dropB n t

/-- What `uncons s` returns: `none` exactly on `""`; otherwise the first code `b` and the rest
    `t`, with `s = cpStr b ++ t`. The last conjunct restates it with `byteStr` for bytes. -/
def UnconsOk (s : String) : Option (Nat × String) → Prop
  | none => s = ""
  | some (b, t) => s.length = t.length + 1 ∧ s = cpStr b ++ t ∧ (b < 256 → s = byteStr b ++ t)

/-- Everything a solver needs to know about the sealed pair. Proved by `spec`; pass it to Blaster
    as a premise. -/
def Spec : Prop :=
  (∀ s, UnconsOk s (uncons s)) ∧
  (∀ c, (cpStr c : String).length = 1) ∧
  (∀ c, c < 256 → cpStr c = byteStr c)

/-! ## Unfolding the sealed pair -/

theorem uncons_eq (s : String) :
    uncons s = (match s.data with | [] => none | c :: cs => some (c.toNat, ⟨cs⟩)) := by
  unfold uncons; unfold instByteViewString; rfl

theorem cpStr_eq (c : Nat) : cpStr c = String.singleton (Char.ofNat c) := by
  unfold cpStr; unfold instByteViewString; rfl

theorem uncons_nil : uncons (String.mk []) = none := by
  rw [uncons_eq]

theorem uncons_cons (c : Char) (cs : List Char) :
    uncons (String.mk (c :: cs)) = some (c.toNat, String.mk cs) := by
  rw [uncons_eq]

theorem cpStr_toNat (c : Char) : cpStr c.toNat = String.singleton c := by
  rw [cpStr_eq, Char.ofNat_toNat]

theorem cpStr_append (c : Char) (cs : List Char) :
    cpStr c.toNat ++ String.mk cs = String.mk (c :: cs) := by
  rw [cpStr_toNat]; rfl

theorem cpStr_length (c : Nat) : (cpStr c : String).length = 1 := by
  rw [cpStr_eq]; rfl

set_option maxRecDepth 100000 in
theorem byteStr_eq : ∀ b, b < 256 → byteStr b = String.singleton (Char.ofNat b) := by
  decide

theorem byteStr_eq_cpStr (b : Nat) (h : b < 256) : byteStr b = cpStr b := by
  rw [byteStr_eq b h, cpStr_eq]

theorem byteStr_length (b : Nat) (h : b < 256) : (byteStr b).length = 1 := by
  rw [byteStr_eq_cpStr b h, cpStr_length]

/-- The sealed pair meets `Spec`. No axioms are involved. -/
theorem spec : Spec := by
  refine ⟨?_, cpStr_length, fun c h => (byteStr_eq_cpStr c h).symm⟩
  intro s
  obtain ⟨l⟩ := s
  cases l with
  | nil => rw [uncons_nil]; rfl
  | cons c cs =>
    rw [uncons_cons]
    have hs := (cpStr_append c cs).symm
    refine ⟨rfl, hs, fun h => ?_⟩
    rw [hs, byteStr_eq_cpStr _ h]

/-! ## `takeB` and `dropB` are `List.take` and `List.drop` -/

theorem dropB_eq (n : Nat) (s : String) : dropB n s = String.mk (s.data.drop n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨l⟩ := s
    cases l with
    | nil => rw [dropB, uncons_nil]; rfl
    | cons c cs => rw [dropB, uncons_cons]; exact ih _

theorem takeB_eq (n : Nat) (s : String) : takeB n s = String.mk (s.data.take n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨l⟩ := s
    cases l with
    | nil => rw [takeB, uncons_nil]; rfl
    | cons c cs => rw [takeB, uncons_cons]; dsimp only; rw [ih, cpStr_append]; rfl

theorem takeB_length_le (n : Nat) (s : String) : (takeB n s).length ≤ n := by
  rw [takeB_eq]
  exact List.length_take_le n s.data

end PlutusCore.Bytes
