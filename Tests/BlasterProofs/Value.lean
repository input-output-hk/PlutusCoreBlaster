import Blaster
import PlutusCore.UPLC
import PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Value (Value)

set_option warn.sorry false

/-!
## Blaster proofs for the `value` builtins

Ports of the `builtin/semantics/{insertCoin,lookupCoin,unionValue,valueContains,
scaleValue,valueData,unValueData}` and `builtin/constant/value` conformance
tests. Each success case pins the exact result (mirroring the conformance
suite's `programsEvalEquiv` check); each `evaluation failure` case proves the
machine reaches `.Error`.

`value` constants are constructed with `cValRaw`, i.e. `fromListD <raw> []`, so
each proof runs the same normalisation (key-sorting, duplicate-summing,
zero/empty pruning, key-length and 128-bit range checks) the textual decoder
performs — the literals below are the raw, pre-normalisation entries exactly as
they appear in the `.uplc` sources. The `illTypedArray`-style `parse error`
constant cases (`ill-formed`, `key-too-long-*`, `overflow`, `underflow`) are
parser-level failures with no CEK counterpart and are noted but not proved.
-/

def ver : Version := ⟨1, 0, 0⟩
def bs (s : String) : ByteString := ⟨s⟩

-- Over-length (33-byte) and maximum-length (32-byte) keys used by a handful of
-- boundary tests.
def key33  : ByteString := ⟨String.mk (List.replicate 33 (Char.ofNat 0xaa))⟩
def key32  : ByteString := ⟨String.mk (List.replicate 32 (Char.ofNat 0xaa))⟩
def key33z : ByteString := ⟨String.mk (List.replicate 33 (Char.ofNat 0))⟩
def key32z : ByteString := ⟨String.mk (List.replicate 32 (Char.ofNat 0))⟩

def cInt  (n : Int)        : Term := .Const (.Integer n)
def cBs   (b : ByteString) : Term := .Const (.ByteString b)
def cData (d : Data)       : Term := .Const (.Data d)
/-- A `value` constant built from raw (pre-normalisation) entries, exactly as
    the textual decoder builds it. -/
def cValRaw (raw : List (ByteString × List (ByteString × Int))) : Term :=
  .Const (.Value (PlutusCore.Value.fromListD raw []))

def app2 (f a b : Term)     : Term := .Apply (.Apply f a) b
def app3 (f a b c : Term)   : Term := .Apply (.Apply (.Apply f a) b) c
def app4 (f a b c d : Term) : Term := .Apply (.Apply (.Apply (.Apply f a) b) c) d

def run (t : Term) : State := cekExecuteProgram ⟨ver, t⟩ [] 1000

-- Signed 128-bit bounds referenced by the overflow / underflow tests.
-- int128Max = 2^127 - 1, int128Min = -2^127.

/-! ### lookupCoin -/

-- present → 100
example : run (app3 (.Builtin .LookupCoin) (cBs (bs "\xaa")) (cBs (bs "\xaa"))
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100)]), (bs "\xbb", [(bs "\xaa", 1)])]))
    = .Halt (.VCon (.Integer 100)) := by blaster

-- absent → 0
example : run (app3 (.Builtin .LookupCoin) (cBs (bs "\xaa")) (cBs (bs "\xbb"))
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100)]), (bs "\xbb", [(bs "\xaa", 1)])]))
    = .Halt (.VCon (.Integer 0)) := by blaster

/-! ### insertCoin -/

-- key-too-long-1: 33-byte currency, non-zero amount → failure
example : run (app4 (.Builtin .InsertCoin) (cBs key33) (cBs (bs "")) (cInt 1) (cValRaw [])) = .Error := by blaster

-- key-too-long-2: 33-byte token, non-zero amount → failure
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs key33) (cInt 1) (cValRaw [])) = .Error := by blaster

-- long-key-zero-1: 33-byte currency but zero amount is allowed (deletes; absent ⇒ no-op)
example : run (app4 (.Builtin .InsertCoin) (cBs key33) (cBs (bs "")) (cInt 0)
    (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 1)])])) := by blaster

-- long-key-zero-2: 33-byte token but zero amount is allowed
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs key33) (cInt 0)
    (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 1)])])) := by blaster

-- multi-ccy-empty: insert a new currency
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "\x00")) (cBs (bs "\x00")) (cInt 1)
    (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 1)]), (bs "\x00", [(bs "\x00", 1)])])) := by blaster

-- multi-ccy-nonempty: overwrite an existing coin (insertCoin sets, not adds)
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "\xaa")) (cBs (bs "\xaa")) (cInt 5)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 1)]), (bs "\xbb", [(bs "\xaa", 1)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 5)]), (bs "\xbb", [(bs "\xaa", 1)])])) := by blaster

-- multi-token: overwrite one token, leaving siblings untouched
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "\xaa")) (cBs (bs "\xbb")) (cInt 10)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 5), (bs "\xbb", 15), (bs "\xcc", 20)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 5), (bs "\xbb", 10), (bs "\xcc", 20)])])) := by blaster

-- negative-empty: negative amount into empty value
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs "")) (cInt (-1)) (cValRaw []))
    = .Halt (.VCon (.Value [(bs "", [(bs "", -1)])])) := by blaster

-- no-overflow: insert the maximum allowed quantity (2^127 - 1)
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs ""))
    (cInt 170141183460469231731687303715884105727) (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 170141183460469231731687303715884105727)])])) := by blaster

-- no-underflow: insert the minimum allowed quantity (-2^127)
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs ""))
    (cInt (-170141183460469231731687303715884105728)) (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Value [(bs "", [(bs "", -170141183460469231731687303715884105728)])])) := by blaster

-- overflow: 2^127 exceeds the maximum → failure
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs ""))
    (cInt 170141183460469231731687303715884105728) (cValRaw [(bs "", [(bs "", 1)])]))
    = .Error := by blaster

-- positive-empty: positive amount into empty value
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs "")) (cInt 1) (cValRaw []))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 1)])])) := by blaster

-- positive-nonempty: overwrite the sole coin
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs "")) (cInt 1)
    (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 1)])])) := by blaster

-- underflow: -2^127 - 1 is below the minimum → failure
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs ""))
    (cInt (-170141183460469231731687303715884105729)) (cValRaw [(bs "", [(bs "", 1)])]))
    = .Error := by blaster

-- zero-positive: inserting 0 deletes the coin, emptying the value
example : run (app4 (.Builtin .InsertCoin) (cBs (bs "")) (cBs (bs "")) (cInt 0)
    (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Value [])) := by blaster

/-! ### scaleValue -/

-- by-neg
example : run (app2 (.Builtin .ScaleValue) (cInt (-2))
    (cValRaw [(bs "\xaa", [(bs "\xaa", 5), (bs "\xbb", -15), (bs "\xcc", 20)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", -10), (bs "\xbb", 30), (bs "\xcc", -40)])])) := by blaster

-- by-pos
example : run (app2 (.Builtin .ScaleValue) (cInt 2)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 5), (bs "\xbb", -15), (bs "\xcc", 20)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 10), (bs "\xbb", -30), (bs "\xcc", 40)])])) := by blaster

-- by-zero: scaling by 0 always yields the empty value
example : run (app2 (.Builtin .ScaleValue) (cInt 0)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 5), (bs "\xbb", -15), (bs "\xcc", 20)])]))
    = .Halt (.VCon (.Value [])) := by blaster

-- no-overflow: 2 * (2^126 - 1) = 2^127 - 2, stays in range
example : run (app2 (.Builtin .ScaleValue) (cInt 2)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 85070591730234615865843651857942052863)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 170141183460469231731687303715884105726)])])) := by blaster

-- no-underflow: 2 * (-2^126) = -2^127, the minimum allowed
example : run (app2 (.Builtin .ScaleValue) (cInt 2)
    (cValRaw [(bs "\xaa", [(bs "\xaa", -85070591730234615865843651857942052864)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", -170141183460469231731687303715884105728)])])) := by blaster

-- overflow: 2 * 2^126 = 2^127 exceeds the maximum → failure
example : run (app2 (.Builtin .ScaleValue) (cInt 2)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 85070591730234615865843651857942052864)])]))
    = .Error := by blaster

-- underflow: 2 * (-2^126 - 1) < -2^127 → failure
example : run (app2 (.Builtin .ScaleValue) (cInt 2)
    (cValRaw [(bs "\xaa", [(bs "\xaa", -85070591730234615865843651857942052865)])]))
    = .Error := by blaster

/-! ### unionValue -/

-- cancel-01: summing to zero prunes the coin
example : run (app2 (.Builtin .UnionValue) (cValRaw [(bs "", [(bs "", 100000)])])
    (cValRaw [(bs "", [(bs "", -100000)])]))
    = .Halt (.VCon (.Value [])) := by blaster

-- cancel-02: order swapped
example : run (app2 (.Builtin .UnionValue) (cValRaw [(bs "", [(bs "", -100000)])])
    (cValRaw [(bs "", [(bs "", 100000)])]))
    = .Halt (.VCon (.Value [])) := by blaster

-- combine
example : run (app2 (.Builtin .UnionValue) (cValRaw [(bs "", [(bs "", 100000)])])
    (cValRaw [(bs "", [(bs "", 100000)])]))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 200000)])])) := by blaster

-- no-overflow: (2^127 - 2) + 1 = 2^127 - 1
example : run (app2 (.Builtin .UnionValue)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 170141183460469231731687303715884105726)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 1)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 170141183460469231731687303715884105727)])])) := by blaster

-- no-underflow: (-2^127 + 1) + (-1) = -2^127
example : run (app2 (.Builtin .UnionValue)
    (cValRaw [(bs "\xaa", [(bs "\xaa", -170141183460469231731687303715884105727)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", -1)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", -170141183460469231731687303715884105728)])])) := by blaster

-- overflow: (2^127 - 1) + 1 = 2^127 → failure
example : run (app2 (.Builtin .UnionValue)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 170141183460469231731687303715884105727)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 1)])]))
    = .Error := by blaster

-- underflow: (-2^127) + (-1) = -2^127 - 1 → failure
example : run (app2 (.Builtin .UnionValue)
    (cValRaw [(bs "\xaa", [(bs "\xaa", -170141183460469231731687303715884105728)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", -1)])]))
    = .Error := by blaster

-- unitl: empty ∪ v = v
example : run (app2 (.Builtin .UnionValue) (cValRaw [])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100000)]), (bs "\xbb", [(bs "\xaa", 125)])]))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 100000)]), (bs "\xbb", [(bs "\xaa", 125)])])) := by blaster

-- unitr: v ∪ empty = v
example : run (app2 (.Builtin .UnionValue)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100000)]), (bs "\xbb", [(bs "\xaa", 125)])]) (cValRaw []))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 100000)]), (bs "\xbb", [(bs "\xaa", 125)])])) := by blaster

/-! ### valueContains

`valueContains A B` checks `A ⊇ B`. Fails if either operand has a negative
quantity. -/

-- ccy-missing → False
example : run (app2 (.Builtin .ValueContains)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 10), (bs "\xbb", 2800)]), (bs "\xff\xff", [(bs "\x88\x88", 100)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 10)]), (bs "\x12\x34", [(bs "\xab\xcd", 20)])]))
    = .Halt (.VCon (.Bool false)) := by blaster

-- multi-insufficient → False
example : run (app2 (.Builtin .ValueContains)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 10), (bs "\xbb", 2800)]), (bs "\xff\xff", [(bs "\x88\x88", 100)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 10)]), (bs "\xff\xff", [(bs "\x88\x88", 101)])]))
    = .Halt (.VCon (.Bool false)) := by blaster

-- multi-sufficient → True
example : run (app2 (.Builtin .ValueContains)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 10), (bs "\xbb", 2800)]), (bs "\xff\xff", [(bs "\x88\x88", 100)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 10)]), (bs "\xff\xff", [(bs "\x88\x88", 20)])]))
    = .Halt (.VCon (.Bool true)) := by blaster

-- neg-empty: first value negative → failure
example : run (app2 (.Builtin .ValueContains)
    (cValRaw [(bs "\xaa", [(bs "\xaa", -100)]), (bs "\xbb", [(bs "\xaa", -1)])]) (cValRaw []))
    = .Error := by blaster

-- neg-neg-eq → failure
example : run (app2 (.Builtin .ValueContains) (cValRaw [(bs "\xaa", [(bs "\xaa", -10)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", -10)])]))
    = .Error := by blaster

-- neg-neg-gt → failure
example : run (app2 (.Builtin .ValueContains) (cValRaw [(bs "\xaa", [(bs "\xaa", -10)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", -9)])]))
    = .Error := by blaster

-- neg-neg-lt → failure
example : run (app2 (.Builtin .ValueContains) (cValRaw [(bs "\xaa", [(bs "\xaa", -10)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", -11)])]))
    = .Error := by blaster

-- neg-pos: first value negative → failure
example : run (app2 (.Builtin .ValueContains) (cValRaw [(bs "\xaa", [(bs "\xaa", -10)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100)])]))
    = .Error := by blaster

-- pos-empty: everything contains the empty value → True
example : run (app2 (.Builtin .ValueContains)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100)]), (bs "\xbb", [(bs "\xaa", 1)])]) (cValRaw []))
    = .Halt (.VCon (.Bool true)) := by blaster

-- pos-neg: second value negative → failure
example : run (app2 (.Builtin .ValueContains) (cValRaw [(bs "\xaa", [(bs "\xaa", 100)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", -10)])]))
    = .Error := by blaster

-- reflexive → True
example : run (app2 (.Builtin .ValueContains)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100)]), (bs "\xbb", [(bs "\xaa", 1)])])
    (cValRaw [(bs "\xaa", [(bs "\xaa", 100)]), (bs "\xbb", [(bs "\xaa", 1)])]))
    = .Halt (.VCon (.Bool true)) := by blaster

-- token-missing → False
example : run (app2 (.Builtin .ValueContains) (cValRaw [(bs "\xaa", [(bs "\xbb", 100), (bs "\xcc", 2800)])])
    (cValRaw [(bs "\xaa", [(bs "\xdd", 5)])]))
    = .Halt (.VCon (.Bool false)) := by blaster

/-! ### valueData -/

-- empty
example : run (.Apply (.Builtin .ValueData) (cValRaw []))
    = .Halt (.VCon (.Data (.Map []))) := by blaster

-- multi-currency
example : run (.Apply (.Builtin .ValueData)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 1)]), (bs "\xbb", [(bs "\xbb", 2)])]))
    = .Halt (.VCon (.Data (.Map
        [(.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 1)]),
         (.B (bs "\xbb"), .Map [(.B (bs "\xbb"), .I 2)])]))) := by blaster

-- multi-token
example : run (.Apply (.Builtin .ValueData)
    (cValRaw [(bs "\xaa", [(bs "\xaa", 5), (bs "\xbb", 10)])]))
    = .Halt (.VCon (.Data (.Map
        [(.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 5), (.B (bs "\xbb"), .I 10)])]))) := by blaster

-- negative-quantity
example : run (.Apply (.Builtin .ValueData) (cValRaw [(bs "", [(bs "", -100)])]))
    = .Halt (.VCon (.Data (.Map [(.B (bs ""), .Map [(.B (bs ""), .I (-100))])]))) := by blaster

-- single-entry
example : run (.Apply (.Builtin .ValueData) (cValRaw [(bs "", [(bs "", 1)])]))
    = .Halt (.VCon (.Data (.Map [(.B (bs ""), .Map [(.B (bs ""), .I 1)])]))) := by blaster

-- roundtrip-from-value: unValueData (valueData v) = v
example : run (.Apply (.Builtin .UnValueData)
    (.Apply (.Builtin .ValueData) (cValRaw [(bs "\xaa", [(bs "\xbb", 100)])])))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xbb", 100)])])) := by blaster

/-! ### unValueData

Inputs are raw `Data` values (not normalised); the decoder enforces the `Value`
invariants and fails otherwise. -/

-- empty
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [])))
    = .Halt (.VCon (.Value [])) := by blaster

-- single-entry
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [(.B (bs ""), .Map [(.B (bs ""), .I 1)])])))
    = .Halt (.VCon (.Value [(bs "", [(bs "", 1)])])) := by blaster

-- multi-currency
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 1)]),
                  (.B (bs "\xbb"), .Map [(.B (bs "\xbb"), .I 2)])])))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 1)]), (bs "\xbb", [(bs "\xbb", 2)])])) := by blaster

-- multi-token
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 5), (.B (bs "\xbb"), .I 10)])])))
    = .Halt (.VCon (.Value [(bs "\xaa", [(bs "\xaa", 5), (bs "\xbb", 10)])])) := by blaster

-- negative-quantity
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [(.B (bs ""), .Map [(.B (bs ""), .I (-100))])])))
    = .Halt (.VCon (.Value [(bs "", [(bs "", -100)])])) := by blaster

-- roundtrip-from-data: valueData (unValueData d) = d
example : run (.Apply (.Builtin .ValueData)
    (.Apply (.Builtin .UnValueData) (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xbb"), .I 100)])]))))
    = .Halt (.VCon (.Data (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xbb"), .I 100)])]))) := by blaster

-- non-map-bytes / non-map-constr / non-map-integer / non-map-list → failure
example : run (.Apply (.Builtin .UnValueData) (cData (.B (bs "\xff")))) = .Error := by blaster
example : run (.Apply (.Builtin .UnValueData) (cData (.Constr 0 [])))   = .Error := by blaster
example : run (.Apply (.Builtin .UnValueData) (cData (.I 42)))          = .Error := by blaster
example : run (.Apply (.Builtin .UnValueData) (cData (.List [])))       = .Error := by blaster

-- non-map-tokens: inner value is I not Map → failure
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [(.B (bs ""), .I 1)]))) = .Error := by blaster

-- non-bytestring-currency: currency key is I → failure
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [(.I 1, .Map [(.B (bs ""), .I 1)])]))) = .Error := by blaster

-- non-bytestring-token: token key is I → failure
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [(.B (bs ""), .Map [(.I 1, .I 1)])]))) = .Error := by blaster

-- non-integer-quantity: quantity is B → failure
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [(.B (bs ""), .Map [(.B (bs ""), .B (bs "\xff"))])]))) = .Error := by blaster

-- data-empty-tokens: inner map is empty → failure
example : run (.Apply (.Builtin .UnValueData) (cData (.Map [(.B (bs "\xaa"), .Map [])]))) = .Error := by blaster

-- data-zero-quantity: a zero quantity is not allowed → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xbb"), .I 0), (.B (bs "\xcc"), .I 100)])])))
    = .Error := by blaster

-- data-unordered-currencies → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xbb"), .Map [(.B (bs "\xaa"), .I 10)]),
                  (.B (bs "\xaa"), .Map [(.B (bs "\xcc"), .I 20)])])))
    = .Error := by blaster

-- data-unordered-tokens → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xcc"), .I 100), (.B (bs "\xbb"), .I 50)])])))
    = .Error := by blaster

-- data-duplicate-currencies → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xbb"), .I 100)]),
                  (.B (bs "\xaa"), .Map [(.B (bs "\xcc"), .I 50)])])))
    = .Error := by blaster

-- data-duplicate-currencies-merge: repeated currency (would sum) → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 123)]),
                  (.B (bs "\xbb"), .Map [(.B (bs "\xbb"), .I 2)]),
                  (.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 80)]),
                  (.B (bs "\xcc"), .Map [(.B (bs "\xcc"), .I 2)]),
                  (.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 43)])])))
    = .Error := by blaster

-- data-duplicate-currencies-cancel: repeated currency (would cancel) → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I 123)]),
                  (.B (bs "\xbb"), .Map [(.B (bs "\xbb"), .I 2)]),
                  (.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I (-80))]),
                  (.B (bs "\xcc"), .Map [(.B (bs "\xcc"), .I 2)]),
                  (.B (bs "\xaa"), .Map [(.B (bs "\xaa"), .I (-43))])])))
    = .Error := by blaster

-- data-zero-sum: repeated token (would sum to zero) → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xbb"), .I 100), (.B (bs "\xbb"), .I (-100))])])))
    = .Error := by blaster

-- data-duplicate-tokens → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs "\xaa"), .Map [(.B (bs "\xbb"), .I 100), (.B (bs "\xbb"), .I 50)])])))
    = .Error := by blaster

-- quantity-overflow: 2^127 > max → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs ""), .Map [(.B (bs ""), .I 170141183460469231731687303715884105728)])])))
    = .Error := by blaster

-- quantity-underflow: -2^127 - 1 < min → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs ""), .Map [(.B (bs ""), .I (-170141183460469231731687303715884105729))])])))
    = .Error := by blaster

-- currency-key-too-long: 33-byte currency → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B key33z, .Map [(.B (bs ""), .I 1)])])))
    = .Error := by blaster

-- token-key-too-long: 33-byte token → failure
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B (bs ""), .Map [(.B key33z, .I 1)])])))
    = .Error := by blaster

-- max-key-len: 32-byte keys are accepted
example : run (.Apply (.Builtin .UnValueData)
    (cData (.Map [(.B key32z, .Map [(.B key32z, .I 1)])])))
    = .Halt (.VCon (.Value [(key32z, [(key32z, 1)])])) := by blaster

/-! ### constant/value

An array/value constant evaluates to its normalised self. The raw entries below
are handed to `fromList`, which sorts, sums duplicates, and prunes zeros and
empty currencies. The `parse error` cases (`ill-formed`, `key-too-long-1`,
`key-too-long-2`, `overflow`, `underflow`) fail in the textual decoder, not the
CEK machine, so they have no proof here. -/

-- empty
example : run (cValRaw []) = .Halt (.VCon (.Value [])) := by blaster

-- empty-tokens: a currency with no tokens is dropped
example : run (cValRaw [(bs "", [])]) = .Halt (.VCon (.Value [])) := by blaster

-- duplicate-keys: quantities summed (123 + 456 = 579)
example : run (cValRaw [(bs "", [(bs "", 123), (bs "", 456)])])
    = .Halt (.VCon (.Value [(bs "", [(bs "", 579)])])) := by blaster

-- zero-asset: zero quantities dropped
example : run (cValRaw [(bs "", [(bs "", 0), (bs "\xaa", 1)])])
    = .Halt (.VCon (.Value [(bs "", [(bs "\xaa", 1)])])) := by blaster

-- no-overflow: quantity 2^127 - 1 accepted
example : run (cValRaw [(bs "", [(bs "", 170141183460469231731687303715884105727)])])
    = .Halt (.VCon (.Value [(bs "", [(bs "", 170141183460469231731687303715884105727)])])) := by blaster

-- no-underflow: quantity -2^127 accepted
example : run (cValRaw [(bs "", [(bs "", -170141183460469231731687303715884105728)])])
    = .Halt (.VCon (.Value [(bs "", [(bs "", -170141183460469231731687303715884105728)])])) := by blaster

-- multi: several currencies and tokens, kept sorted
example : run (cValRaw [(bs "", [(bs "", 123), (bs "\xbb", 50000)]),
                        (bs "\xff\xff", [(bs "\xaa", -10), (bs "\xbb", 20)])])
    = .Halt (.VCon (.Value [(bs "", [(bs "", 123), (bs "\xbb", 50000)]),
                            (bs "\xff\xff", [(bs "\xaa", -10), (bs "\xbb", 20)])])) := by blaster

-- unordered: entries get sorted by key
example : run (cValRaw [(bs "\xff\xff", [(bs "\xbb", 123), (bs "\xaa", 456)]),
                        (bs "\xaa", [(bs "\xaa", 123)]),
                        (bs "", [(bs "\xaa", 123)])])
    = .Halt (.VCon (.Value [(bs "", [(bs "\xaa", 123)]),
                            (bs "\xaa", [(bs "\xaa", 123)]),
                            (bs "\xff\xff", [(bs "\xaa", 456), (bs "\xbb", 123)])])) := by blaster

-- max-key-length-1: 32-byte token key accepted and sorted after the empty key
example : run (cValRaw [(bs "", [(key32, 123), (bs "", 456)])])
    = .Halt (.VCon (.Value [(bs "", [(bs "", 456), (key32, 123)])])) := by blaster

-- max-key-length-2: 32-byte currency key accepted, duplicate tokens summed
example : run (cValRaw [(key32, [(bs "", 123), (bs "", 456)])])
    = .Halt (.VCon (.Value [(key32, [(bs "", 579)])])) := by blaster
