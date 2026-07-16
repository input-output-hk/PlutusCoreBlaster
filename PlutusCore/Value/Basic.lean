import PlutusCore.ByteString
import PlutusCore.Data
import PlutusCore.Integer

/-!
## PlutusCore `Value` builtin type

Mirrors `PlutusCore.Value` from the Haskell implementation. A `Value` is a
nested map `currency → (token → quantity)` where:

* currency and token bytestrings are at most 32 bytes;
* quantities are signed 128-bit integers (`-2^127 .. 2^127 - 1`);
* no inner map is empty;
* no quantity is zero.

The smart constructor `fromList` is what the textual parser uses: it merges
duplicate `(currency, token)` pairs by summing quantities (re-checking the
128-bit bound for the sum), drops zero quantities and empty currencies, and
sorts by key. The builtin operations (`insertCoin`, `lookupCoin`,
`unionValue`, `valueContains`, `scaleValue`, `valueData`, `unValueData`)
preserve those invariants.

### Representation note

The backing store is a plain sorted association `List`, *not* `Std.TreeMap`.
The `TreeMap` representation is opaque to the Blaster SMT tactic (its optimizer
cannot reduce the `Std.Data.DTreeMap` comparator lambdas), which blocks any
proof mentioning a non-empty `Value`. A sorted `List` reduces cleanly, mirroring
the earlier switch of the `array` backing store to `List`. Every operation below
keeps the list strictly sorted by key with no empty inner maps and no zero
quantities, so structural list equality coincides with `Value` equality.
-/

namespace PlutusCore.Value

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

/-- Inner map: token name → quantity, as a list sorted strictly ascending by
    token with no zero quantities. -/
abbrev Tokens := List (ByteString × Integer)

/-- Outer map: currency symbol → tokens, as a list sorted strictly ascending by
    currency with no empty inner maps. -/
abbrev Value := List (ByteString × Tokens)

namespace Internal

-- ---------------------------------------------------------------------------
-- Constants and validity
-- ---------------------------------------------------------------------------

/-- Maximum length (in bytes) of a currency-symbol or token-name key. -/
def maxKeyLen : Nat := 32

/-- Inclusive lower bound of a signed 128-bit integer: `-2^127`. -/
def int128Min : Integer := -170141183460469231731687303715884105728

/-- Inclusive upper bound of a signed 128-bit integer: `2^127 - 1`. -/
def int128Max : Integer :=  170141183460469231731687303715884105727

/-- Maximum `totalSize` accepted by `valueData`. -/
def valueDataMaxSize : Nat := 40000

@[inline] def validKey (bs : ByteString) : Bool := bs.data.length ≤ maxKeyLen
@[inline] def validQuantity (i : Integer) : Bool := int128Min ≤ i && i ≤ int128Max

/-- Total order on keys, lexicographic on the underlying bytes. Matches
    `Ord ByteString` (`compare x.data y.data`) but is expressed with `String.<`
    and `==` so the Blaster optimizer can reduce it. -/
@[inline] def keyCmp (a b : ByteString) : Ordering :=
  if a.data < b.data then .lt else if a.data == b.data then .eq else .gt

-- ---------------------------------------------------------------------------
-- Sorted association-list primitives (shared by the outer and inner maps)
-- ---------------------------------------------------------------------------

namespace AList

variable {α : Type}

/-- Lookup in a key-sorted association list. -/
def get? (k : ByteString) : List (ByteString × α) → Option α
  | []            => none
  | (k', v) :: xs =>
    match keyCmp k k' with
    | .lt => none          -- keys are sorted, so `k` cannot appear later
    | .eq => some v
    | .gt => get? k xs

/-- Lookup with a default. -/
def getD (k : ByteString) (l : List (ByteString × α)) (d : α) : α :=
  match get? k l with
  | some v => v
  | none   => d

/-- Insert (replacing any existing entry), keeping the list key-sorted. -/
def insert (k : ByteString) (v : α) : List (ByteString × α) → List (ByteString × α)
  | []             => [(k, v)]
  | (k', v') :: xs =>
    match keyCmp k k' with
    | .lt => (k, v) :: (k', v') :: xs
    | .eq => (k, v) :: xs
    | .gt => (k', v') :: insert k v xs

/-- Erase a key, keeping the list key-sorted. -/
def erase (k : ByteString) : List (ByteString × α) → List (ByteString × α)
  | []             => []
  | (k', v') :: xs =>
    match keyCmp k k' with
    | .lt => (k', v') :: xs -- keys are sorted, so `k` cannot appear later
    | .eq => xs
    | .gt => (k', v') :: erase k xs

end AList

-- ---------------------------------------------------------------------------
-- Basic operations
-- ---------------------------------------------------------------------------

/-- The empty `Value`. -/
def empty : Value := []

/-- `true` iff `v` has no entries. -/
def isEmpty (v : Value) : Bool :=
  match v with
  | [] => true
  | _  => false

/-- Sum of inner-map sizes — used as the cost-model size of a `Value`. -/
def totalSize : Value → Nat
  | []             => 0
  | (_, ts) :: rest => ts.length + totalSize rest

/-- Size of the largest inner map (0 if empty). -/
def maxInnerSize : Value → Nat
  | []             => 0
  | (_, ts) :: rest => max ts.length (maxInnerSize rest)

private def tokensAnyNeg : Tokens → Bool
  | []            => false
  | (_, q) :: rest => (q < 0) || tokensAnyNeg rest

/-- Returns true, if there exists at least one negative quantity
    across all entries. -/
def anyNegativeAmounts : Value → Bool
  | []              => false
  | (_, ts) :: rest => tokensAnyNeg ts || anyNegativeAmounts rest

/-- Flatten `v` into a list of `((currency, token), quantity)` triples in
    ascending key order. -/
def toFlatList (v : Value) : List (ByteString × ByteString × Integer) :=
  v.flatMap (fun (cur, ts) => ts.map (fun (tok, amt) => (cur, tok, amt)))

/-- Convert `v` to its nested association-list form. With the list backing
    store this is the identity. -/
def toAssocList (v : Value) : List (ByteString × List (ByteString × Integer)) := v

-- ---------------------------------------------------------------------------
-- Equality
-- ---------------------------------------------------------------------------

-- Every operation keeps the list in canonical sorted/normalised form, so the
-- structural `List` equality supplied automatically for `Value` coincides with
-- `Value` equality; no bespoke `BEq` instance is required.

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

/-- Insert `tok ↦ q` into `inner` if non-zero, otherwise erase `tok`. -/
@[inline] private def insertOrErase (inner : Tokens) (tok : ByteString) (q : Integer) : Tokens :=
  if q == 0 then AList.erase tok inner else AList.insert tok q inner

/-- Replace `cur`'s inner map with `inner`, or erase `cur` if `inner` is empty. -/
@[inline] private def setOrPrune (outer : Value) (cur : ByteString) (inner : Tokens) : Value :=
  match inner with
  | [] => AList.erase cur outer
  | _  => AList.insert cur inner outer

-- ---------------------------------------------------------------------------
-- fromList — smart constructor used by the parser
-- ---------------------------------------------------------------------------

private def fromListAddAssets : Tokens → List (ByteString × Integer) → Except String Tokens
  | inner, []                 => pure inner
  | inner, (tok, amt) :: rest => do
      if ¬ validKey tok then
        throw "Token name exceeds maximum length of 32 bytes"
      if ¬ validQuantity amt then
        throw "Token quantity out of signed 128-bit integer bounds"
      let summed := AList.getD tok inner 0 + amt
      if ¬ validQuantity summed then
        throw "Token quantity out of signed 128-bit integer bounds after merging duplicates"
      fromListAddAssets (insertOrErase inner tok summed) rest

private def fromListAddEntries : Value → List (ByteString × List (ByteString × Integer)) → Except String Value
  | outer, []                   => pure outer
  | outer, (cur, assets) :: rest => do
      if ¬ validKey cur then
        throw "Currency symbol exceeds maximum length of 32 bytes"
      let inner ← fromListAddAssets (AList.getD cur outer []) assets
      fromListAddEntries (setOrPrune outer cur inner) rest

/-- Build a `Value` from an unnormalised association list. Validates lengths
    and quantity ranges, sums duplicate `(currency, token)` quantities (and
    re-checks the bound), and drops zero quantities and empty currencies.
    Mirrors Haskell's `Value.fromList`. -/
def fromList (entries : List (ByteString × List (ByteString × Integer))) : Except String Value :=
  fromListAddEntries [] entries

/-- Like `fromList`, but returns `default` on any validation failure. Intended
    for round-tripping `toAssocList`/`ToExpr`, where the input is guaranteed
    valid. -/
@[inline] def fromListD (entries : List (ByteString × List (ByteString × Integer))) (default : Value) : Value :=
  match fromList entries with
  | .ok v    => v
  | .error _ => default

-- ---------------------------------------------------------------------------
-- Builtin functions
-- ---------------------------------------------------------------------------

/-- Delete the asset at `(cur, tok)` from `v`, pruning the inner map if it
    becomes empty. -/
def deleteCoin (cur tok : ByteString) (v : Value) : Value :=
  match AList.get? cur v with
  | none       => v
  | some inner => setOrPrune v cur (AList.erase tok inner)

/-- `insertCoin currency token amount value`. -/
def insertCoin (cur tok : ByteString) (amt : Integer) (v : Value) : Except String Value :=
  if amt == 0 then
    pure (deleteCoin cur tok v)
  else if ¬ validKey cur then
    throw "insertCoin: invalid currency"
  else if ¬ validKey tok then
    throw "insertCoin: invalid token"
  else if ¬ validQuantity amt then
    throw "insertCoin: quantity out of bounds"
  else
    let inner := AList.insert tok amt (AList.getD cur v [])
    pure (AList.insert cur inner v)

/-- `lookupCoin currency token value` — total; returns 0 when absent. -/
def lookupCoin (cur tok : ByteString) (v : Value) : Integer :=
  match AList.get? cur v with
  | none       => 0
  | some inner => AList.getD tok inner 0

private def unionInner (innerA : Tokens) : Tokens → Except String Tokens
  | []             => pure innerA
  | (tok, q) :: rest => do
      let summed := AList.getD tok innerA 0 + q
      if ¬ validQuantity summed then
        throw "unionValue: quantity is out of the signed 128-bit integer bounds"
      unionInner (insertOrErase innerA tok summed) rest

private def unionOuter (acc : Value) : Value → Except String Value
  | []                  => pure acc
  | (cur, innerB) :: rest => do
      let innerA := AList.getD cur acc []
      let merged ← unionInner innerA innerB
      unionOuter (setOrPrune acc cur merged) rest

/-- Add two values, summing quantities at matching keys. Fails on overflow. -/
def unionValue (a b : Value) : Except String Value :=
  if isEmpty a then pure b
  else if isEmpty b then pure a
  else unionOuter a b

private def innerContained (innerA : Tokens) : Tokens → Bool
  | []             => true
  | (tok, q) :: rest =>
      (match AList.get? tok innerA with
       | none    => false
       | some q' => q ≤ q')
      && innerContained innerA rest

private def outerContained (a : Value) : Value → Bool
  | []                  => true
  | (cur, innerB) :: rest =>
      (match AList.get? cur a with
       | none        => innerB.isEmpty
       | some innerA => innerContained innerA innerB)
      && outerContained a rest

/-- Check `a ⊇ b`: every `(currency, token, qty)` in `b` satisfies
    `lookupCoin currency token a ≥ qty`. Fails if either side has any
    negative quantity. -/
def valueContains (a b : Value) : Except String Bool :=
  if anyNegativeAmounts a then
    throw "valueContains: first value contains negative amounts"
  else if anyNegativeAmounts b then
    throw "valueContains: second value contains negative amounts"
  else if totalSize a < totalSize b then
    pure false
  else
    pure (outerContained a b)

private def scaleInner (c : Integer) : Tokens → Except String Tokens
  | []             => pure []
  | (tok, q) :: rest => do
      let s := c * q
      if ¬ validQuantity s then
        throw "scaleValue: quantity out of bounds"
      let rest' ← scaleInner c rest
      pure ((tok, s) :: rest')

private def scaleOuter (c : Integer) : Value → Except String Value
  | []               => pure []
  | (cur, inner) :: rest => do
      let inner' ← scaleInner c inner
      let rest' ← scaleOuter c rest
      pure (match inner' with
            | [] => rest'
            | _  => (cur, inner') :: rest')

/-- Multiply every quantity by `c`. Scaling by 0 always yields the empty value
    (never fails). Otherwise fails on overflow. -/
def scaleValue (c : Integer) (v : Value) : Except String Value :=
  if c == 0 then pure []
  else scaleOuter c v

private def tokensToData : Tokens → List (Data × Data)
  | []             => []
  | (tok, q) :: rest => (Data.B tok, Data.I q) :: tokensToData rest

private def valueToDataEntries : Value → List (Data × Data)
  | []               => []
  | (cur, inner) :: rest => (Data.B cur, Data.Map (tokensToData inner)) :: valueToDataEntries rest

/-- Encode `v` as nested `Data.Map`s. Fails if `totalSize v > 40000`. -/
def valueData (v : Value) : Except String Data :=
  if valueDataMaxSize < totalSize v then
    throw "valueData: maximum input size (40000) exceeded"
  else
    pure (.Map (valueToDataEntries v))

-- Parse one `B <bytestring>` key, enforcing the length invariant. Factored out
-- of the recursive walkers below so their bodies stay in the flat
-- `let x ← helper; …` shape that Blaster's unfold-theorem generation supports
-- (inlining these as `let x ← match … pure/throw` blocks the tactic).
private def parseKey (d : Data) : Except String ByteString :=
  match d with
  | .B b => if validKey b then .ok b else .error "unValueData: invalid key"
  | _    => .error "unValueData: non-B key"

-- Parse one `I <integer>` quantity, enforcing the range invariant.
private def parseQty (d : Data) : Except String Integer :=
  match d with
  | .I i => if validQuantity i then .ok i else .error "unValueData: quantity out of bounds"
  | _    => .error "unValueData: non-I quantity"

-- Enforce strict-ascending key order against the previous key (if any).
private def checkAscending (prev : Option ByteString) (k : ByteString) : Except String Unit :=
  match prev with
  | some p => match keyCmp p k with
              | .lt => .ok ()
              | _   => .error "unValueData: keys not strictly ascending"
  | none   => .ok ()

-- Walk an outer entry of the nested `Map`-of-`Map` form into an inner map,
-- enforcing strict-ascending tokens, non-zero quantities, and the key/range
-- invariants (mirrors Haskell `buildValueWith`'s inner loop). The output list
-- is built in the (verified strictly-ascending) input order.
private def unValueDataInner : Option ByteString → List (Data × Data) → Except String Tokens
  | _   , []             => .ok []
  | prev, (tD, qD) :: rest => do
      let tok ← parseKey tD
      let q ← parseQty qD
      if q == 0 then
        throw "unValueData: zero quantity"
      let _ ← checkAscending prev tok
      let rest' ← unValueDataInner (some tok) rest
      .ok ((tok, q) :: rest')

private def parseInner (d : Data) : Except String Tokens :=
  match d with
  | .Map ts => unValueDataInner none ts
  | _       => .error "unValueData: inner tokens not a Map"

private def unValueDataOuter : Option ByteString → List (Data × Data) → Except String Value
  | _   , []             => .ok []
  | prev, (cD, tsD) :: rest => do
      let cur ← parseKey cD
      let inner ← parseInner tsD
      if inner.isEmpty then
        throw "unValueData: empty inner map"
      let _ ← checkAscending prev cur
      let rest' ← unValueDataOuter (some cur) rest
      .ok ((cur, inner) :: rest')

/-- Decode `Data` into a `Value`, enforcing the same invariants that
    `valueData` produces. -/
def unValueData (d : Data) : Except String Value :=
  match d with
  | .Map outer => unValueDataOuter none outer
  | _          => throw "unValueData: non-Map constructor"

end Internal

export Internal
  (
    -- basic functions
    anyNegativeAmounts
    empty
    fromList
    fromListD
    isEmpty
    maxInnerSize
    toAssocList
    toFlatList
    totalSize
    -- builtin function implementations
    deleteCoin
    insertCoin
    lookupCoin
    scaleValue
    unionValue
    unValueData
    valueContains
    valueData
  )

end PlutusCore.Value
