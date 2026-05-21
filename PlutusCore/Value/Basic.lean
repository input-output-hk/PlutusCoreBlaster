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
-/

namespace PlutusCore.Value

open Std
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

/-- Inner map: token name → quantity. -/
abbrev Tokens := TreeMap ByteString Integer

/-- Outer map: currency symbol → tokens. -/
abbrev Value := TreeMap ByteString Tokens

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

-- ---------------------------------------------------------------------------
-- Basic operations
-- ---------------------------------------------------------------------------

/-- The empty `Value`. -/
def empty : Value := TreeMap.empty

/-- `true` iff `v` has no entries. -/
def isEmpty (v : Value) : Bool := v.isEmpty

/-- Sum of inner-map sizes — used as the cost-model size of a `Value`. -/
def totalSize (v : Value) : Nat :=
  v.foldl (λ acc _ ts => acc + ts.size) 0

/-- Size of the largest inner map (0 if empty). -/
def maxInnerSize (v : Value) : Nat :=
  v.foldl (λ acc _ ts => max acc ts.size) 0

/-- Returns true, if there exists at least one negative quantity
    across all entries. -/
def anyNegativeAmounts (v : Value) : Bool :=
  v.any (λ _ b => b.any (λ _ x => x < 0))

/-- Flatten `v` into a list of `((currency, token), quantity)` triples in
    ascending key order. -/
def toFlatList (v : Value) : List (ByteString × ByteString × Integer) :=
  v.toList.flatMap (λ (cur, ts) =>
    ts.toList.map (λ (tok, amt) => (cur, tok, amt)))

/-- Convert `v` to its nested association-list form. -/
def toAssocList (v : Value) : List (ByteString × List (ByteString × Integer)) :=
  v.toList.map (λ (cur, ts) => (cur, ts.toList))

-- ---------------------------------------------------------------------------
-- Equality
-- ---------------------------------------------------------------------------

private def tokensBeq (a b : Tokens) : Bool :=
  if a.size == b.size
    then a.all (λ k v => b.get? k == some v)
    else false

private def valueBeq (a b : Value) : Bool :=
  if a.size == b.size
    then a.all (λ k v => Option.getD (tokensBeq v <$> b.get? k) false)
    else false

instance : BEq Value := ⟨valueBeq⟩

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

/-- Insert `tok ↦ summed` into `inner` if non-zero, otherwise erase `tok`. -/
@[inline] private def insertOrErase (inner : Tokens) (tok : ByteString) (q : Integer) : Tokens :=
  if q == 0 then inner.erase tok else inner.insert tok q

/-- Replace `cur`'s inner map with `inner`, or erase `cur` if `inner` is empty. -/
@[inline] private def setOrPrune (outer : Value) (cur : ByteString) (inner : Tokens) : Value :=
  if inner.isEmpty then outer.erase cur else outer.insert cur inner

-- ---------------------------------------------------------------------------
-- fromList — smart constructor used by the parser
-- ---------------------------------------------------------------------------

private def fromListAddAsset (inner : Tokens) (entry : ByteString × Integer) : Except String Tokens := do
  let (tok, amt) := entry
  if ¬ validKey tok then
    throw s!"Token name exceeds maximum length of {maxKeyLen} bytes (got {tok.data.length})"
  if ¬ validQuantity amt then
    throw s!"Token quantity out of signed 128-bit integer bounds: {amt}"
  let summed := (inner.getD tok 0) + amt
  if ¬ validQuantity summed then
    throw s!"Token quantity out of signed 128-bit integer bounds after merging duplicates: {summed}"
  pure (insertOrErase inner tok summed)

private def fromListAddEntry (outer : Value) (entry : ByteString × List (ByteString × Integer)) : Except String Value := do
  let (cur, assets) := entry
  if ¬ validKey cur then
    throw s!"Currency symbol exceeds maximum length of {maxKeyLen} bytes (got {cur.data.length})"
  let inner ← assets.foldlM fromListAddAsset (outer.getD cur TreeMap.empty)
  pure (setOrPrune outer cur inner)

/-- Build a `Value` from an unnormalised association list. Validates lengths
    and quantity ranges, sums duplicate `(currency, token)` quantities (and
    re-checks the bound), and drops zero quantities and empty currencies.
    Mirrors Haskell's `Value.fromList`. -/
def fromList (entries : List (ByteString × List (ByteString × Integer))) : Except String Value :=
  entries.foldlM fromListAddEntry empty

/-- Like `fromList`, but returns `empty` on any validation failure. Intended
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
  match v.get? cur with
  | none       => v
  | some inner => setOrPrune v cur (inner.erase tok)

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
    let inner := (v.getD cur TreeMap.empty).insert tok amt
    pure (v.insert cur inner)

/-- `lookupCoin currency token value` — total; returns 0 when absent. -/
def lookupCoin (cur tok : ByteString) (v : Value) : Integer :=
  match v.get? cur with
  | none       => 0
  | some inner => inner.getD tok 0

private def unionInner (innerA innerB : Tokens) : Except String Tokens :=
  innerB.foldlM (init := innerA) (λ inner tok q => do
    let summed := (inner.getD tok 0) + q
    if ¬ validQuantity summed then
      throw "unionValue: quantity is out of the signed 128-bit integer bounds"
    pure (insertOrErase inner tok summed))

/-- Add two values, summing quantities at matching keys. Fails on overflow. -/
def unionValue (a b : Value) : Except String Value := do
  if isEmpty a then return b
  if isEmpty b then return a
  b.foldlM (init := a) (λ outer cur innerB => do
    let innerA := outer.getD cur TreeMap.empty
    let merged ← unionInner innerA innerB
    pure (setOrPrune outer cur merged))

/-- Check `a ⊇ b`: every `(currency, token, qty)` in `b` satisfies
    `lookupCoin currency token a ≥ qty`. Fails if either side has any
    negative quantity. -/
def valueContains (a b : Value) : Except String Bool := do
  if anyNegativeAmounts a then
    throw "valueContains: first value contains negative amounts"
  if anyNegativeAmounts b then
    throw "valueContains: second value contains negative amounts"
  if totalSize a < totalSize b then return false
  pure (b.all (λ cur innerB =>
    match a.get? cur with
    | none        => innerB.isEmpty
    | some innerA =>
        innerB.all (λ tok q =>
          match innerA.get? tok with
          | none    => false
          | some q' => q ≤ q')))

private def scaleInner (c : Integer) (inner : Tokens) : Except String Tokens :=
  inner.foldlM (init := (TreeMap.empty : Tokens)) (λ acc tok q => do
    let s := c * q
    if ¬ validQuantity s then
      throw s!"scaleValue: quantity out of bounds: {c} * {q}"
    pure (acc.insert tok s))

/-- Multiply every quantity by `c`. Scaling by 0 always yields the empty value
    (never fails). Otherwise fails on overflow. -/
def scaleValue (c : Integer) (v : Value) : Except String Value := do
  if c == 0 then return empty
  v.foldlM (init := empty) (λ outer cur inner => do
    let inner' ← scaleInner c inner
    -- inner' is empty iff inner was empty, which the invariant rules out;
    -- still be defensive in case the invariant ever drifts.
    pure (if inner'.isEmpty then outer else outer.insert cur inner'))

/-- Encode `v` as nested `Data.Map`s. Fails if `totalSize v > 40000`. -/
def valueData (v : Value) : Except String Data := do
  if valueDataMaxSize < totalSize v then
    throw s!"valueData: maximum input size ({valueDataMaxSize}) exceeded"
  let outer :=
    v.toList.map (λ (cur, inner) =>
      let inner' := inner.toList.map (λ (tok, q) => (.B tok, .I q))
      (.B cur, .Map inner'))
  pure (.Map outer)

-- Walk an outer entry of the nested `Map`-of-`Map` form into an inner map,
-- enforcing strict-ascending tokens, non-zero quantities, and the key/range
-- invariants (mirrors Haskell `buildValueWith`'s inner loop).
private def unValueDataInner : Option ByteString → Tokens → List (Data × Data) → Except String Tokens
  | _   , acc, [] => pure acc
  | prev, acc, (tD, qD) :: rest => do
      let tok ← match tD with
        | .B b => if validKey b then pure b
                  else throw "unValueData: invalid key"
        | _    => throw "unValueData: non-B token key"
      let q ← match qD with
        | .I i => if validQuantity i then pure i
                  else throw "unValueData: quantity out of bounds"
        | _    => throw "unValueData: non-I quantity"
      if q == 0 then
        throw "unValueData: zero quantity"
      match prev with
      | some p =>
          if ¬ p < tok then
            throw "unValueData: token names not strictly ascending"
      | none   => pure ()
      unValueDataInner (some tok) (acc.insert tok q) rest

private def unValueDataOuter : Option ByteString → Value → List (Data × Data) → Except String Value
  | _   , acc, [] => pure acc
  | prev, acc, (cD, tsD) :: rest => do
      let cur ← match cD with
        | .B b => if validKey b then pure b
                  else throw "unValueData: invalid currency key"
        | _    => throw "unValueData: non-B currency key"
      let inner ← match tsD with
        | .Map ts => unValueDataInner none TreeMap.empty ts
        | _       => throw "unValueData: inner tokens not a Map"
      if inner.isEmpty then
        throw "unValueData: empty inner map"
      match prev with
      | some p =>
          if ¬ p < cur then
            throw "unValueData: currency symbols not strictly ascending"
      | none   => pure ()
      unValueDataOuter (some cur) (acc.insert cur inner) rest

/-- Decode `Data` into a `Value`, enforcing the same invariants that
    `valueData` produces. -/
def unValueData (d : Data) : Except String Value := do
  match d with
  | .Map outer => unValueDataOuter none empty outer
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
