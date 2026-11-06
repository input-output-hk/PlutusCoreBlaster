/-! # Byte-level access to `String`-carried byte strings, in a form Blaster can translate

`ByteString` and the Plutus `string` type are both carried by a Lean `String`. Blaster maps
`String` to the SMT string sort, where `++`, `String.length`, `=`, `<`, `≤` and string literals
are native. Anything that reaches a `Char` (`String.data`, `Char.ofNat`, `Char.toNat`, `UInt8`)
unfolds to `UInt32`, `BitVec` and `Fin`, which Blaster cannot translate for a symbolic string.

The builtins that touch individual bytes therefore go through this module only:

* **Writers** build bytes with `byteStr k`, the one-byte string with code `k < 256`.
* **Readers** take strings apart with `uncons` and rebuild characters with `cpStr`.

These three are the only primitives that look at characters. Their single instance,
`instByteViewString`, is `@[irreducible]`, which Blaster treats as a seal: all three become
uninterpreted functions. Every builtin is ordinary recursion and arithmetic over them (`takeB`,
`dropB` and the builtins), so Blaster still sees the real algorithm. `byteStr` is sealed too, even
though it involves no `Char` (it looks the byte up in a list of 256 string literals): left open,
that lookup reaches the solver as a recursive function over the list, and z3 does not settle a
goal that reads back a byte written by it.

`Spec` states what a solver needs to know about the sealed primitives, and `spec` proves it without
axioms. Blaster does not pick up theorems, so a goal that reads bytes from a symbolic string takes
`Spec` as a premise:

```
#blaster [PlutusCore.Bytes.Spec → ∀ (s : String), (sliceByteString 0 2 ⟨s⟩).length ≤ 2]
```

The seal costs two things.
* Blaster no longer evaluates a builtin that reads or writes bytes on a literal; the solver has to
  work it out from `Spec`. A module that only needs concrete evaluation can lift the seal with
  `attribute [local semireducible] PlutusCore.Bytes.instByteViewString`.
* `rfl` and `decide` stop at the seal too. `with_unfolding_all rfl`, `decide +kernel`,
  `native_decide`, `#eval` and `#guard` all still evaluate these builtins.

Compiled code (`#eval`, `#guard`, `native_decide`) does not run `uncons`, `takeB`, `dropB`,
`byteStr` and `repB` as written, which would turn the rest of the string into a `List Char` and
back at every byte, walk the table, or take a stack frame per byte. `@[csimp]` theorems
(`unconsString_eq_fast`, `takeB_eq_impl`, `dropB_eq_impl`, `byteOfTable_eq_impl`, `repB_eq_impl`)
replace them with equal functions that work on the UTF-8 bytes or take a single pass. The loops of
the builtins get the same treatment where they are defined: each is followed by a tail-recursive
version over the `List Char` and a `@[csimp]` theorem, since `uncons` copies the rest of the
string. Being theorems, they add nothing to what has to be trusted.
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

/-- The one-byte string with code `k`, for `k < 256` (`""` otherwise): `byteStr` before the seal. -/
def byteOfTable (k : Nat) : String := byteTable.getD k ""

set_option maxRecDepth 100000 in
theorem byteOfTable_eq : ∀ b, b < 256 → byteOfTable b = String.singleton (Char.ofNat b) := by
  decide

set_option maxRecDepth 10000 in
theorem byteTable_length : byteTable.length = 256 := rfl

set_option maxRecDepth 10000 in
theorem byteOfTable_add_256 (m : Nat) : byteOfTable (m + 256) = "" := rfl

theorem byteOfTable_of_ge (k : Nat) (h : 256 ≤ k) : byteOfTable k = "" := by
  obtain ⟨j, hj⟩ := Nat.le.dest h
  rw [← hj, Nat.add_comm]
  exact byteOfTable_add_256 j

/-- `byteOfTable` for compiled code, without walking the table; `byteOfTable_eq_impl` makes the
    compiler use it. It precedes the instance, which is compiled with it. -/
def byteOfTableImpl (k : Nat) : String := if k < 256 then String.singleton (Char.ofNat k) else ""

@[csimp] theorem byteOfTable_eq_impl : @byteOfTable = @byteOfTableImpl := by
  funext k
  unfold byteOfTableImpl
  split
  · exact byteOfTable_eq k ‹_›
  · exact byteOfTable_of_ge k (by omega)

/-- What `uncons` returns for a non-empty string: the code of its first character and the rest.

    It is a structure rather than the pair `Nat × String` on purpose. Blaster (at the pinned commit)
    can give the type parameters of two parametric datatypes in one query each other's names: with
    `Prod` and `Except`, or `Prod` and BLS12-381's `Point`, z3 then rejects the query ("invalid
    datatype declaration, unknown sort"). A structure without parameters cannot be mixed up. -/
structure Cell where
  /-- The code of the first character. -/
  code : Nat
  /-- The rest of the string. -/
  rest : String

/-- The character-level view of a string. The class exists only so that its one instance can be
    sealed: Blaster honours `@[irreducible]` on an instance, but not on a plain `def`. It has no
    type parameter, so that `Cell` needs none either. -/
class ByteView where
  /-- The code of the first character and the rest, or `none` for the empty string. -/
  uncons  : String → Option Cell
  /-- The one-character string with the given code. -/
  cpStr   : Nat → String
  /-- The one-byte string with code `k`, for `k < 256` (`""` otherwise). -/
  byteStr : Nat → String

/-- `uncons` on `String`: the code of the first character and the rest. -/
def unconsString (s : String) : Option Cell :=
  match s.data with
  | [] => none
  | c :: cs => some ⟨c.toNat, ⟨cs⟩⟩

/-- `unconsString` for compiled code: it reads the first character and copies the rest of the
    UTF-8 bytes, instead of turning the whole string into a `List Char` and back.
    `unconsString_eq_fast` makes the compiler use it in place of `unconsString`. -/
def unconsStringFast (s : String) : Option Cell :=
  if s.utf8ByteSize = 0 then none
  else some ⟨(s.get 0).toNat, s.extract (s.next 0) s.endPos⟩

theorem extract_go₂_utf8ByteSize (l : List Char) (i : String.Pos) :
    String.extract.go₂ l i ⟨i.byteIdx + String.utf8ByteSize.go l⟩ = l := by
  induction l generalizing i with
  | nil => rfl
  | cons c cs ih =>
    have hc := Char.utf8Size_pos c
    have hgo : String.utf8ByteSize.go (c :: cs) = String.utf8ByteSize.go cs + c.utf8Size := rfl
    have hne : i ≠ ⟨i.byteIdx + String.utf8ByteSize.go (c :: cs)⟩ := by
      intro h; have := congrArg String.Pos.byteIdx h; simp only [hgo] at this; omega
    rw [String.extract.go₂, if_neg hne]
    have h2 : (⟨i.byteIdx + String.utf8ByteSize.go (c :: cs)⟩ : String.Pos)
        = ⟨(i + c).byteIdx + String.utf8ByteSize.go cs⟩ := by
      rw [hgo]; show (⟨_⟩ : String.Pos) = ⟨i.byteIdx + c.utf8Size + _⟩; congr 1; omega
    rw [h2, ih]

/-- Extracting from just after the first character to the end gives the rest. -/
theorem extract_tail (c : Char) (cs : List Char) :
    String.extract ⟨c :: cs⟩ ⟨c.utf8Size⟩ (String.endPos ⟨c :: cs⟩) = ⟨cs⟩ := by
  have hc := Char.utf8Size_pos c
  have hsz : (String.endPos ⟨c :: cs⟩).byteIdx = String.utf8ByteSize.go cs + c.utf8Size := rfl
  show (if _ then _ else _) = _
  cases cs with
  | nil => rw [if_pos (by show c.utf8Size ≥ 0 + c.utf8Size; omega)]
  | cons d ds =>
    have hd := Char.utf8Size_pos d
    have hgo : String.utf8ByteSize.go (d :: ds) = String.utf8ByteSize.go ds + d.utf8Size := rfl
    rw [if_neg (by rw [hsz, hgo]; show ¬ c.utf8Size ≥ _; omega)]
    congr 1
    have h0 : (0 : String.Pos) ≠ ⟨c.utf8Size⟩ := by
      intro h; have := congrArg String.Pos.byteIdx h; simp only [String.Pos.byteIdx_zero] at this; omega
    have h1 : (0 : String.Pos) + c = ⟨c.utf8Size⟩ := by
      show (⟨0 + c.utf8Size⟩ : String.Pos) = _; congr 1; omega
    rw [String.extract.go₁, if_neg h0, String.extract.go₁, if_pos h1]
    have he : String.endPos ⟨c :: d :: ds⟩
        = ⟨((0 : String.Pos) + c).byteIdx + String.utf8ByteSize.go (d :: ds)⟩ := by
      show String.Pos.mk (String.utf8ByteSize.go (d :: ds) + c.utf8Size)
        = String.Pos.mk (0 + c.utf8Size + String.utf8ByteSize.go (d :: ds))
      congr 1; omega
    rw [he, extract_go₂_utf8ByteSize]

/-- Compiled code runs `unconsStringFast` for `unconsString`. It precedes the instance, which is
    compiled with it. -/
@[csimp] theorem unconsString_eq_fast : @unconsString = @unconsStringFast := by
  funext s
  obtain ⟨l⟩ := s
  cases l with
  | nil => rfl
  | cons c cs =>
    have hc := Char.utf8Size_pos c
    have hsz : String.utf8ByteSize ⟨c :: cs⟩ = String.utf8ByteSize.go cs + c.utf8Size := rfl
    have hget : String.get ⟨c :: cs⟩ 0 = c := by simp [String.get, String.utf8GetAux]
    have hnext : String.next ⟨c :: cs⟩ 0 = ⟨c.utf8Size⟩ := by
      show (0 : String.Pos) + String.get ⟨c :: cs⟩ 0 = _
      rw [hget]; show (⟨0 + c.utf8Size⟩ : String.Pos) = _; congr 1; omega
    rw [unconsStringFast, if_neg (by rw [hsz]; omega), hget, hnext, extract_tail]
    rfl

/-- The sealed instance. The kernel still unfolds it, so everything about it stays provable. -/
@[irreducible] instance instByteViewString : ByteView where
  uncons := unconsString
  cpStr c := String.singleton (Char.ofNat c)
  byteStr := byteOfTable

export ByteView (uncons cpStr byteStr)

/-- The first `n` characters of `s` (all of `s` when it is shorter). -/
def takeB : Nat → String → String
  | 0, _ => ""
  | n + 1, s =>
    match uncons s with
    | none => ""
    | some ⟨b, t⟩ => cpStr b ++ takeB n t

/-- `s` without its first `n` characters (`""` when it is shorter). -/
def dropB : Nat → String → String
  | 0, s => s
  | n + 1, s =>
    match uncons s with
    | none => ""
    | some ⟨_, t⟩ => dropB n t

/-- `n` copies of the byte `b` (`b < 256`). -/
def repB : Nat → Nat → String
  | 0, _ => ""
  | n + 1, b => byteStr b ++ repB n b

set_option maxRecDepth 20000 in
/-- The value of `byteStr` at every byte, as 256 plain facts. The seal stops Blaster from
    evaluating `byteStr` on a literal; with these, the solver can still work out the bytes a
    builtin writes, or reads, on literal inputs. Facts about literals cost a solver little, unlike
    the table lookup they replace. -/
def ByteTable : Prop :=
  byteStr 0x00 = "\x00" ∧ byteStr 0x01 = "\x01" ∧ byteStr 0x02 = "\x02" ∧ byteStr 0x03 = "\x03" ∧ byteStr 0x04 = "\x04" ∧ byteStr 0x05 = "\x05" ∧ byteStr 0x06 = "\x06" ∧ byteStr 0x07 = "\x07" ∧
  byteStr 0x08 = "\x08" ∧ byteStr 0x09 = "\x09" ∧ byteStr 0x0a = "\x0a" ∧ byteStr 0x0b = "\x0b" ∧ byteStr 0x0c = "\x0c" ∧ byteStr 0x0d = "\x0d" ∧ byteStr 0x0e = "\x0e" ∧ byteStr 0x0f = "\x0f" ∧
  byteStr 0x10 = "\x10" ∧ byteStr 0x11 = "\x11" ∧ byteStr 0x12 = "\x12" ∧ byteStr 0x13 = "\x13" ∧ byteStr 0x14 = "\x14" ∧ byteStr 0x15 = "\x15" ∧ byteStr 0x16 = "\x16" ∧ byteStr 0x17 = "\x17" ∧
  byteStr 0x18 = "\x18" ∧ byteStr 0x19 = "\x19" ∧ byteStr 0x1a = "\x1a" ∧ byteStr 0x1b = "\x1b" ∧ byteStr 0x1c = "\x1c" ∧ byteStr 0x1d = "\x1d" ∧ byteStr 0x1e = "\x1e" ∧ byteStr 0x1f = "\x1f" ∧
  byteStr 0x20 = "\x20" ∧ byteStr 0x21 = "\x21" ∧ byteStr 0x22 = "\x22" ∧ byteStr 0x23 = "\x23" ∧ byteStr 0x24 = "\x24" ∧ byteStr 0x25 = "\x25" ∧ byteStr 0x26 = "\x26" ∧ byteStr 0x27 = "\x27" ∧
  byteStr 0x28 = "\x28" ∧ byteStr 0x29 = "\x29" ∧ byteStr 0x2a = "\x2a" ∧ byteStr 0x2b = "\x2b" ∧ byteStr 0x2c = "\x2c" ∧ byteStr 0x2d = "\x2d" ∧ byteStr 0x2e = "\x2e" ∧ byteStr 0x2f = "\x2f" ∧
  byteStr 0x30 = "\x30" ∧ byteStr 0x31 = "\x31" ∧ byteStr 0x32 = "\x32" ∧ byteStr 0x33 = "\x33" ∧ byteStr 0x34 = "\x34" ∧ byteStr 0x35 = "\x35" ∧ byteStr 0x36 = "\x36" ∧ byteStr 0x37 = "\x37" ∧
  byteStr 0x38 = "\x38" ∧ byteStr 0x39 = "\x39" ∧ byteStr 0x3a = "\x3a" ∧ byteStr 0x3b = "\x3b" ∧ byteStr 0x3c = "\x3c" ∧ byteStr 0x3d = "\x3d" ∧ byteStr 0x3e = "\x3e" ∧ byteStr 0x3f = "\x3f" ∧
  byteStr 0x40 = "\x40" ∧ byteStr 0x41 = "\x41" ∧ byteStr 0x42 = "\x42" ∧ byteStr 0x43 = "\x43" ∧ byteStr 0x44 = "\x44" ∧ byteStr 0x45 = "\x45" ∧ byteStr 0x46 = "\x46" ∧ byteStr 0x47 = "\x47" ∧
  byteStr 0x48 = "\x48" ∧ byteStr 0x49 = "\x49" ∧ byteStr 0x4a = "\x4a" ∧ byteStr 0x4b = "\x4b" ∧ byteStr 0x4c = "\x4c" ∧ byteStr 0x4d = "\x4d" ∧ byteStr 0x4e = "\x4e" ∧ byteStr 0x4f = "\x4f" ∧
  byteStr 0x50 = "\x50" ∧ byteStr 0x51 = "\x51" ∧ byteStr 0x52 = "\x52" ∧ byteStr 0x53 = "\x53" ∧ byteStr 0x54 = "\x54" ∧ byteStr 0x55 = "\x55" ∧ byteStr 0x56 = "\x56" ∧ byteStr 0x57 = "\x57" ∧
  byteStr 0x58 = "\x58" ∧ byteStr 0x59 = "\x59" ∧ byteStr 0x5a = "\x5a" ∧ byteStr 0x5b = "\x5b" ∧ byteStr 0x5c = "\x5c" ∧ byteStr 0x5d = "\x5d" ∧ byteStr 0x5e = "\x5e" ∧ byteStr 0x5f = "\x5f" ∧
  byteStr 0x60 = "\x60" ∧ byteStr 0x61 = "\x61" ∧ byteStr 0x62 = "\x62" ∧ byteStr 0x63 = "\x63" ∧ byteStr 0x64 = "\x64" ∧ byteStr 0x65 = "\x65" ∧ byteStr 0x66 = "\x66" ∧ byteStr 0x67 = "\x67" ∧
  byteStr 0x68 = "\x68" ∧ byteStr 0x69 = "\x69" ∧ byteStr 0x6a = "\x6a" ∧ byteStr 0x6b = "\x6b" ∧ byteStr 0x6c = "\x6c" ∧ byteStr 0x6d = "\x6d" ∧ byteStr 0x6e = "\x6e" ∧ byteStr 0x6f = "\x6f" ∧
  byteStr 0x70 = "\x70" ∧ byteStr 0x71 = "\x71" ∧ byteStr 0x72 = "\x72" ∧ byteStr 0x73 = "\x73" ∧ byteStr 0x74 = "\x74" ∧ byteStr 0x75 = "\x75" ∧ byteStr 0x76 = "\x76" ∧ byteStr 0x77 = "\x77" ∧
  byteStr 0x78 = "\x78" ∧ byteStr 0x79 = "\x79" ∧ byteStr 0x7a = "\x7a" ∧ byteStr 0x7b = "\x7b" ∧ byteStr 0x7c = "\x7c" ∧ byteStr 0x7d = "\x7d" ∧ byteStr 0x7e = "\x7e" ∧ byteStr 0x7f = "\x7f" ∧
  byteStr 0x80 = "\x80" ∧ byteStr 0x81 = "\x81" ∧ byteStr 0x82 = "\x82" ∧ byteStr 0x83 = "\x83" ∧ byteStr 0x84 = "\x84" ∧ byteStr 0x85 = "\x85" ∧ byteStr 0x86 = "\x86" ∧ byteStr 0x87 = "\x87" ∧
  byteStr 0x88 = "\x88" ∧ byteStr 0x89 = "\x89" ∧ byteStr 0x8a = "\x8a" ∧ byteStr 0x8b = "\x8b" ∧ byteStr 0x8c = "\x8c" ∧ byteStr 0x8d = "\x8d" ∧ byteStr 0x8e = "\x8e" ∧ byteStr 0x8f = "\x8f" ∧
  byteStr 0x90 = "\x90" ∧ byteStr 0x91 = "\x91" ∧ byteStr 0x92 = "\x92" ∧ byteStr 0x93 = "\x93" ∧ byteStr 0x94 = "\x94" ∧ byteStr 0x95 = "\x95" ∧ byteStr 0x96 = "\x96" ∧ byteStr 0x97 = "\x97" ∧
  byteStr 0x98 = "\x98" ∧ byteStr 0x99 = "\x99" ∧ byteStr 0x9a = "\x9a" ∧ byteStr 0x9b = "\x9b" ∧ byteStr 0x9c = "\x9c" ∧ byteStr 0x9d = "\x9d" ∧ byteStr 0x9e = "\x9e" ∧ byteStr 0x9f = "\x9f" ∧
  byteStr 0xa0 = "\xa0" ∧ byteStr 0xa1 = "\xa1" ∧ byteStr 0xa2 = "\xa2" ∧ byteStr 0xa3 = "\xa3" ∧ byteStr 0xa4 = "\xa4" ∧ byteStr 0xa5 = "\xa5" ∧ byteStr 0xa6 = "\xa6" ∧ byteStr 0xa7 = "\xa7" ∧
  byteStr 0xa8 = "\xa8" ∧ byteStr 0xa9 = "\xa9" ∧ byteStr 0xaa = "\xaa" ∧ byteStr 0xab = "\xab" ∧ byteStr 0xac = "\xac" ∧ byteStr 0xad = "\xad" ∧ byteStr 0xae = "\xae" ∧ byteStr 0xaf = "\xaf" ∧
  byteStr 0xb0 = "\xb0" ∧ byteStr 0xb1 = "\xb1" ∧ byteStr 0xb2 = "\xb2" ∧ byteStr 0xb3 = "\xb3" ∧ byteStr 0xb4 = "\xb4" ∧ byteStr 0xb5 = "\xb5" ∧ byteStr 0xb6 = "\xb6" ∧ byteStr 0xb7 = "\xb7" ∧
  byteStr 0xb8 = "\xb8" ∧ byteStr 0xb9 = "\xb9" ∧ byteStr 0xba = "\xba" ∧ byteStr 0xbb = "\xbb" ∧ byteStr 0xbc = "\xbc" ∧ byteStr 0xbd = "\xbd" ∧ byteStr 0xbe = "\xbe" ∧ byteStr 0xbf = "\xbf" ∧
  byteStr 0xc0 = "\xc0" ∧ byteStr 0xc1 = "\xc1" ∧ byteStr 0xc2 = "\xc2" ∧ byteStr 0xc3 = "\xc3" ∧ byteStr 0xc4 = "\xc4" ∧ byteStr 0xc5 = "\xc5" ∧ byteStr 0xc6 = "\xc6" ∧ byteStr 0xc7 = "\xc7" ∧
  byteStr 0xc8 = "\xc8" ∧ byteStr 0xc9 = "\xc9" ∧ byteStr 0xca = "\xca" ∧ byteStr 0xcb = "\xcb" ∧ byteStr 0xcc = "\xcc" ∧ byteStr 0xcd = "\xcd" ∧ byteStr 0xce = "\xce" ∧ byteStr 0xcf = "\xcf" ∧
  byteStr 0xd0 = "\xd0" ∧ byteStr 0xd1 = "\xd1" ∧ byteStr 0xd2 = "\xd2" ∧ byteStr 0xd3 = "\xd3" ∧ byteStr 0xd4 = "\xd4" ∧ byteStr 0xd5 = "\xd5" ∧ byteStr 0xd6 = "\xd6" ∧ byteStr 0xd7 = "\xd7" ∧
  byteStr 0xd8 = "\xd8" ∧ byteStr 0xd9 = "\xd9" ∧ byteStr 0xda = "\xda" ∧ byteStr 0xdb = "\xdb" ∧ byteStr 0xdc = "\xdc" ∧ byteStr 0xdd = "\xdd" ∧ byteStr 0xde = "\xde" ∧ byteStr 0xdf = "\xdf" ∧
  byteStr 0xe0 = "\xe0" ∧ byteStr 0xe1 = "\xe1" ∧ byteStr 0xe2 = "\xe2" ∧ byteStr 0xe3 = "\xe3" ∧ byteStr 0xe4 = "\xe4" ∧ byteStr 0xe5 = "\xe5" ∧ byteStr 0xe6 = "\xe6" ∧ byteStr 0xe7 = "\xe7" ∧
  byteStr 0xe8 = "\xe8" ∧ byteStr 0xe9 = "\xe9" ∧ byteStr 0xea = "\xea" ∧ byteStr 0xeb = "\xeb" ∧ byteStr 0xec = "\xec" ∧ byteStr 0xed = "\xed" ∧ byteStr 0xee = "\xee" ∧ byteStr 0xef = "\xef" ∧
  byteStr 0xf0 = "\xf0" ∧ byteStr 0xf1 = "\xf1" ∧ byteStr 0xf2 = "\xf2" ∧ byteStr 0xf3 = "\xf3" ∧ byteStr 0xf4 = "\xf4" ∧ byteStr 0xf5 = "\xf5" ∧ byteStr 0xf6 = "\xf6" ∧ byteStr 0xf7 = "\xf7" ∧
  byteStr 0xf8 = "\xf8" ∧ byteStr 0xf9 = "\xf9" ∧ byteStr 0xfa = "\xfa" ∧ byteStr 0xfb = "\xfb" ∧ byteStr 0xfc = "\xfc" ∧ byteStr 0xfd = "\xfd" ∧ byteStr 0xfe = "\xfe" ∧ byteStr 0xff = "\xff"

/-- What `uncons s` returns: `none` exactly on `""`; otherwise the first code `b` and the rest
    `t`, with `s = cpStr b ++ t`. The last conjunct restates it with `byteStr` for bytes. -/
def UnconsOk (s : String) : Option Cell → Prop
  | none => s = ""
  | some ⟨b, t⟩ => s.length = t.length + 1 ∧ s = cpStr b ++ t ∧ (b < 256 → s = byteStr b ++ t)

/-- Everything a solver needs to know about the sealed primitives. Proved by `spec`; pass it to
    Blaster as a premise. In proofs, use the accessors (`Spec.unconsOk` and so on) rather than the
    position of a conjunct.

    The fourth conjunct fixes the code that `uncons` returns for a string that starts with a byte.
    `UnconsOk` alone does not: it relates that code to the string only through `cpStr`, which is
    pinned down for codes below 256 only, so a solver could take `cpStr 261 = "\x05"` and read
    `"\x05"` as 261. -/
def Spec : Prop :=
  (∀ s, UnconsOk s (uncons s)) ∧
  (∀ c, (cpStr c : String).length = 1) ∧
  (∀ c, c < 256 → cpStr c = byteStr c) ∧
  (∀ b t, b < 256 → uncons (byteStr b ++ t) = some ⟨b, t⟩) ∧
  (∀ k, 256 ≤ k → byteStr k = "") ∧
  ByteTable

theorem Spec.unconsOk (h : Spec) : ∀ s, UnconsOk s (uncons s) := h.1
theorem Spec.cpStr_length (h : Spec) : ∀ c, (cpStr c : String).length = 1 := h.2.1
theorem Spec.cpStr_eq_byteStr (h : Spec) : ∀ c, c < 256 → cpStr c = byteStr c := h.2.2.1
theorem Spec.uncons_byteStr_append (h : Spec) :
    ∀ b t, b < 256 → uncons (byteStr b ++ t) = some ⟨b, t⟩ := h.2.2.2.1
theorem Spec.byteStr_of_ge (h : Spec) : ∀ k, 256 ≤ k → byteStr k = "" := h.2.2.2.2.1
theorem Spec.byteTable (h : Spec) : ByteTable := h.2.2.2.2.2

theorem Spec.uncons_byteStr (h : Spec) (b : Nat) (hb : b < 256) :
    uncons (byteStr b) = some ⟨b, ""⟩ := by
  have := h.uncons_byteStr_append b "" hb
  rwa [String.append_empty] at this

theorem Spec.byteStr_length (h : Spec) (b : Nat) (hb : b < 256) : (byteStr b).length = 1 := by
  rw [← h.cpStr_eq_byteStr b hb]; exact h.cpStr_length b

/-! ## Unfolding the sealed primitives -/

theorem uncons_eq (s : String) :
    uncons s = (match s.data with | [] => none | c :: cs => some ⟨c.toNat, ⟨cs⟩⟩) := by
  unfold uncons; unfold instByteViewString; rfl

theorem cpStr_eq (c : Nat) : cpStr c = String.singleton (Char.ofNat c) := by
  unfold cpStr; unfold instByteViewString; rfl

theorem byteStr_def (k : Nat) : byteStr k = byteOfTable k := by
  unfold byteStr; unfold instByteViewString; rfl

theorem uncons_nil : uncons (String.mk []) = none := by
  rw [uncons_eq]

theorem uncons_cons (c : Char) (cs : List Char) :
    uncons (String.mk (c :: cs)) = some ⟨c.toNat, String.mk cs⟩ := by
  rw [uncons_eq]

theorem cpStr_toNat (c : Char) : cpStr c.toNat = String.singleton c := by
  rw [cpStr_eq, Char.ofNat_toNat]

theorem cpStr_append (c : Char) (cs : List Char) :
    cpStr c.toNat ++ String.mk cs = String.mk (c :: cs) := by
  rw [cpStr_toNat]; rfl

theorem cpStr_length (c : Nat) : (cpStr c : String).length = 1 := by
  rw [cpStr_eq]; rfl

theorem byteStr_eq (b : Nat) (h : b < 256) : byteStr b = String.singleton (Char.ofNat b) := by
  rw [byteStr_def, byteOfTable_eq b h]

theorem byteStr_of_ge (k : Nat) (h : 256 ≤ k) : byteStr k = "" := by
  rw [byteStr_def, byteOfTable_of_ge k h]

theorem byteStr_eq_cpStr (b : Nat) (h : b < 256) : byteStr b = cpStr b := by
  rw [byteStr_eq b h, cpStr_eq]

theorem byteStr_length (b : Nat) (h : b < 256) : (byteStr b).length = 1 := by
  rw [byteStr_eq_cpStr b h, cpStr_length]

theorem toNat_ofNat_byte (b : Nat) (h : b < 256) : (Char.ofNat b).toNat = b := by
  have hv : b.isValidChar := Or.inl (Nat.lt_trans h (by decide))
  rw [Char.ofNat, dif_pos hv]
  rfl

theorem uncons_byteStr_append (b : Nat) (t : String) (h : b < 256) :
    uncons (byteStr b ++ t) = some ⟨b, t⟩ := by
  rw [byteStr_eq b h]
  show uncons (String.mk (Char.ofNat b :: t.data)) = _
  rw [uncons_cons, toNat_ofNat_byte b h]

set_option maxRecDepth 20000 in
theorem byteTable_holds : ByteTable := by
  unfold ByteTable
  and_intros <;> with_unfolding_all rfl

/-- The sealed primitives meet `Spec`. No axioms are involved. -/
theorem spec : Spec := by
  refine ⟨?_, cpStr_length, fun c h => (byteStr_eq_cpStr c h).symm, uncons_byteStr_append,
    byteStr_of_ge, byteTable_holds⟩
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

/-- `takeB` for compiled code, in one pass over the characters; `takeB_eq_impl` makes the compiler
    use it. -/
def takeBImpl (n : Nat) (s : String) : String := String.mk (s.data.take n)

/-- `dropB` for compiled code, in one pass over the characters; `dropB_eq_impl` makes the compiler
    use it. -/
def dropBImpl (n : Nat) (s : String) : String := String.mk (s.data.drop n)

@[csimp] theorem takeB_eq_impl : @takeB = @takeBImpl := by
  funext n s; exact takeB_eq n s

@[csimp] theorem dropB_eq_impl : @dropB = @dropBImpl := by
  funext n s; exact dropB_eq n s

/-! ## `repB` is `List.replicate` -/

theorem repB_eq (n b : Nat) (h : b < 256) : repB n b = String.mk (List.replicate n (Char.ofNat b)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repB, ih, byteStr_eq b h]; rfl

/-- `acc ++ repB n b`, tail recursively, for compiled code. -/
def repBGo : Nat → Nat → String → String
  | 0    , _, acc => acc
  | n + 1, b, acc => repBGo n b (acc ++ byteStr b)

theorem repBGo_eq (n b : Nat) (acc : String) : repBGo n b acc = acc ++ repB n b := by
  induction n generalizing acc with
  | zero => rw [repBGo, repB, String.append_empty]
  | succ n ih => rw [repBGo, ih, repB, String.append_assoc]

/-- `repB` for compiled code, without a stack frame per byte; `repB_eq_impl` makes the compiler use
    it. -/
def repBImpl (n b : Nat) : String := repBGo n b ""

@[csimp] theorem repB_eq_impl : @repB = @repBImpl := by
  funext n b; rw [repBImpl, repBGo_eq, String.empty_append]

end PlutusCore.Bytes
