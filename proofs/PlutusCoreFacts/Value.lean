import PlutusCore.Value.Basic
import Blaster

/-!
Value-map invariants and per-asset lookup equations, including successful
insertion, deletion, union, containment, and Data encoding/decoding.
The theorems state their sortedness and success premises explicitly.
-/

namespace PlutusCore.Value
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)
namespace Internal

section BlasterFacts
open PlutusCore.Data (Data)
set_option maxHeartbeats 0
-- one Blaster proof at a time (each runs its own solver process)
set_option Elab.async false

/-- Strictly ascending keys after an optional lower bound. -/
def ascending {α : Type} (prev : Option ByteString) : List (ByteString × α) → Bool
  | [] => true
  | (k, _) :: rest => above prev k && ascending (some k) rest
where
  above : Option ByteString → ByteString → Bool
    | some p, k => keyCmp p k == .lt
    | none, _ => true

@[blaster_library] theorem get?_insert (prev : Option ByteString) (k k' : ByteString) (v : Integer)
    (l : List (ByteString × Integer)) :
    ascending prev l = true →
    AList.get? k (AList.insert k' v l) = if k = k' then some v else AList.get? k l := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem get?_erase (prev : Option ByteString) (k k' : ByteString)
    (l : List (ByteString × Integer)) :
    ascending prev l = true →
    AList.get? k (AList.erase k' l) = if k = k' then none else AList.get? k l := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_insert (prev : Option ByteString) (k : ByteString) (v : Integer)
    (l : List (ByteString × Integer)) :
    ascending prev l = true → ascending.above prev k = true →
    ascending prev (AList.insert k v l) = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_erase (prev : Option ByteString) (k : ByteString)
    (l : List (ByteString × Integer)) :
    ascending prev l = true → ascending prev (AList.erase k l) = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem get?_below (p k : ByteString) (l : List (ByteString × Integer)) :
    ascending (some p) l = true → keyCmp p k ≠ .lt → AList.get? k l = none := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem getD_insertOrErase (prev : Option ByteString) (t tok : ByteString) (q : Integer)
    (inner : Tokens) :
    ascending prev inner = true →
    AList.getD t (insertOrErase inner tok q) 0 = if t = tok then q else AList.getD t inner 0 := by
  blaster (induction: auto) (summaries: [get?_insert, get?_erase]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_insertOrErase (tok : ByteString) (q : Integer) (inner : Tokens) :
    ascending none inner = true → ascending none (insertOrErase inner tok q) = true := by
  blaster (induction: auto) (summaries: [ascending_insert, ascending_erase]) (timeout: 20) (gen-cex: 0)

/-- Merging a token map preserves strictly ascending keys. -/
@[blaster_library] theorem unionInner_ascending (innerA innerB r : Tokens) :
    ascending none innerA = true → unionInner innerA innerB = .ok r → ascending none r = true := by
  blaster (induction: auto) (summaries: [ascending_insertOrErase]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unionInner_getD (prev : Option ByteString) (t : ByteString) (innerA innerB r : Tokens) :
    ascending none innerA = true → ascending prev innerB = true →
    unionInner innerA innerB = .ok r →
    AList.getD t r 0 = AList.getD t innerA 0 + AList.getD t innerB 0 := by
  blaster (induction: auto)
    (summaries: [getD_insertOrErase, ascending_insertOrErase, get?_below]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem get?_insertV (prev : Option ByteString) (k k' : ByteString) (v : Tokens) (l : Value) :
    ascending prev l = true →
    AList.get? k (AList.insert k' v l) = if k = k' then some v else AList.get? k l := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem get?_eraseV (prev : Option ByteString) (k k' : ByteString) (l : Value) :
    ascending prev l = true →
    AList.get? k (AList.erase k' l) = if k = k' then none else AList.get? k l := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_insertV (prev : Option ByteString) (k : ByteString) (v : Tokens) (l : Value) :
    ascending prev l = true → ascending.above prev k = true →
    ascending prev (AList.insert k v l) = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_eraseV (prev : Option ByteString) (k : ByteString) (l : Value) :
    ascending prev l = true → ascending prev (AList.erase k l) = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem get?_belowV (p k : ByteString) (l : Value) :
    ascending (some p) l = true → keyCmp p k ≠ .lt → AList.get? k l = none := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- Every inner map is strictly ascending. -/
def innersAscending : Value → Bool
  | [] => true
  | (_, inner) :: rest => ascending none inner && innersAscending rest

@[blaster_library] theorem innersAscending_insert (k : ByteString) (v : Tokens) (l : Value) :
    innersAscending l = true → ascending none v = true →
    innersAscending (AList.insert k v l) = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem innersAscending_erase (k : ByteString) (l : Value) :
    innersAscending l = true → innersAscending (AList.erase k l) = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem innersAscending_get? (k : ByteString) (l : Value) (inner : Tokens) :
    innersAscending l = true → AList.get? k l = some inner → ascending none inner = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem get?_setOrPrune (k c : ByteString) (inner : Tokens) (l : Value) :
    ascending none l = true →
    AList.get? k (setOrPrune l c inner) =
      if k = c then (match inner with | [] => none | _ => some inner) else AList.get? k l := by
  blaster (induction: auto) (summaries: [get?_insertV, get?_eraseV]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_setOrPrune (c : ByteString) (inner : Tokens) (l : Value) :
    ascending none l = true → ascending none (setOrPrune l c inner) = true := by
  blaster (induction: auto) (summaries: [ascending_insertV, ascending_eraseV]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem innersAscending_setOrPrune (c : ByteString) (inner : Tokens) (l : Value) :
    innersAscending l = true → ascending none inner = true →
    innersAscending (setOrPrune l c inner) = true := by
  blaster (induction: auto) (summaries: [innersAscending_insert, innersAscending_erase]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem getD_ascending (k : ByteString) (l : Value) :
    innersAscending l = true → ascending none (AList.getD k l []) = true := by
  blaster (induction: auto) (summaries: [innersAscending_get?]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unionOuter_ascending (acc b r : Value) :
    ascending none acc = true → unionOuter acc b = .ok r → ascending none r = true := by
  blaster (induction: auto) (summaries: [ascending_setOrPrune]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unionOuter_inners (acc b r : Value) :
    innersAscending acc = true → innersAscending b = true →
    unionOuter acc b = .ok r → innersAscending r = true := by
  blaster (induction: auto)
    (summaries: [innersAscending_setOrPrune, unionInner_ascending, getD_ascending]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem lookupCoin_setOrPrune (c t cur : ByteString) (merged : Tokens) (l : Value) :
    ascending none l = true →
    lookupCoin c t (setOrPrune l cur merged) =
      if c = cur then AList.getD t merged 0 else lookupCoin c t l := by
  blaster (induction: auto) (summaries: [get?_setOrPrune]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem lookupCoin_cons (prev : Option ByteString) (c t cur : ByteString) (inner : Tokens) (rest : Value) :
    ascending prev ((cur, inner) :: rest) = true →
    lookupCoin c t ((cur, inner) :: rest) =
      if c = cur then AList.getD t inner 0 else lookupCoin c t rest := by
  blaster (induction: auto) (summaries: [get?_belowV]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem getD_getD (c t : ByteString) (l : Value) :
    AList.getD t (AList.getD c l []) 0 = lookupCoin c t l := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unionOuter_lookup (prev : Option ByteString) (c t : ByteString) (acc b r : Value) :
    ascending none acc = true → innersAscending acc = true →
    ascending prev b = true → innersAscending b = true →
    unionOuter acc b = .ok r →
    lookupCoin c t r = lookupCoin c t acc + lookupCoin c t b := by
  blaster (induction: auto)
    (summaries: [lookupCoin_setOrPrune, lookupCoin_cons, unionInner_getD, getD_ascending, getD_getD,
      ascending_setOrPrune, innersAscending_setOrPrune, unionInner_ascending, get?_belowV]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem lookupCoin_deleteCoin (c t c0 t0 : ByteString) (v : Value) :
    ascending none v = true → innersAscending v = true →
    lookupCoin c t (deleteCoin c0 t0 v) = if c = c0 ∧ t = t0 then 0 else lookupCoin c t v := by
  blaster (induction: auto)
    (summaries: [lookupCoin_setOrPrune, get?_erase, innersAscending_get?, getD_getD]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_deleteCoin (c0 t0 : ByteString) (v : Value) :
    ascending none v = true → ascending none (deleteCoin c0 t0 v) = true := by
  blaster (induction: auto) (summaries: [ascending_setOrPrune]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem innersAscending_deleteCoin (c0 t0 : ByteString) (v : Value) :
    innersAscending v = true → innersAscending (deleteCoin c0 t0 v) = true := by
  blaster (induction: auto)
    (summaries: [innersAscending_setOrPrune, ascending_erase, innersAscending_get?]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem lookupCoin_insertCoin (c t c0 t0 : ByteString) (q : Integer) (v w : Value) :
    ascending none v = true → innersAscending v = true →
    insertCoin c0 t0 q v = .ok w →
    lookupCoin c t w = if c = c0 ∧ t = t0 then q else lookupCoin c t v := by
  blaster (induction: auto)
    (summaries: [lookupCoin_deleteCoin, get?_insertV, get?_insert, getD_ascending, getD_getD]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem ascending_insertCoin (c0 t0 : ByteString) (q : Integer) (v w : Value) :
    ascending none v = true → insertCoin c0 t0 q v = .ok w → ascending none w = true := by
  blaster (induction: auto) (summaries: [ascending_deleteCoin, ascending_insertV]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem innersAscending_insertCoin (c0 t0 : ByteString) (q : Integer) (v w : Value) :
    innersAscending v = true → insertCoin c0 t0 q v = .ok w → innersAscending w = true := by
  blaster (induction: auto)
    (summaries: [innersAscending_deleteCoin, innersAscending_insert, ascending_insert, getD_ascending])
    (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem getD_nonneg (t : ByteString) (inner : Tokens) :
    tokensAnyNeg inner = false → 0 ≤ AList.getD t inner 0 := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem innerContained_getD (prev : Option ByteString) (t : ByteString) (innerA innerB : Tokens) :
    ascending none innerA = true → ascending prev innerB = true → tokensAnyNeg innerA = false →
    innerContained innerA innerB = true → AList.getD t innerB 0 ≤ AList.getD t innerA 0 := by
  blaster (induction: auto) (summaries: [getD_nonneg, get?_below]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem anyNegativeAmounts_get? (k : ByteString) (l : Value) (inner : Tokens) :
    anyNegativeAmounts l = false → AList.get? k l = some inner → tokensAnyNeg inner = false := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem lookupCoin_nonneg (c t : ByteString) (a : Value) :
    anyNegativeAmounts a = false → 0 ≤ lookupCoin c t a := by
  blaster (induction: auto) (summaries: [anyNegativeAmounts_get?, getD_nonneg]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem outerContained_lookup (prev : Option ByteString) (c t : ByteString) (a b : Value) :
    ascending none a = true → innersAscending a = true →
    ascending prev b = true → innersAscending b = true →
    anyNegativeAmounts a = false → outerContained a b = true → lookupCoin c t b ≤ lookupCoin c t a := by
  blaster (induction: auto)
    (summaries: [innerContained_getD, lookupCoin_cons, innersAscending_get?, anyNegativeAmounts_get?,
      lookupCoin_nonneg]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem valueContains_lookup (c t : ByteString) (a b : Value) :
    ascending none a = true → innersAscending a = true →
    ascending none b = true → innersAscending b = true →
    valueContains a b = .ok true → lookupCoin c t b ≤ lookupCoin c t a := by
  blaster (induction: auto) (summaries: [outerContained_lookup]) (timeout: 20) (gen-cex: 0)

/-- The quantity of `(cur, tok)` in a nested `Data` map (first match), as the
ledger's `valueOf` computes it. -/
def findToken (tok : ByteString) : List (Data × Data) → Integer
  | [] => 0
  | (rTok, rQ) :: rest =>
      if Data.B tok = rTok then
        match rQ with
        | Data.I q => q
        | _ => 0
      else findToken tok rest

def dataQuantity (cur tok : ByteString) : List (Data × Data) → Integer
  | [] => 0
  | (rCur, Data.Map tokens) :: rest =>
      if Data.B cur == rCur then findToken tok tokens else dataQuantity cur tok rest
  | _ => 0

@[blaster_library] theorem unValueDataInner_ascending (prev : Option ByteString) (ts : List (Data × Data)) (inner : Tokens) :
    unValueDataInner prev ts = .ok inner → ascending prev inner = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unValueDataInner_getD (prev : Option ByteString) (t : ByteString) (ts : List (Data × Data)) (inner : Tokens) :
    unValueDataInner prev ts = .ok inner → AList.getD t inner 0 = findToken t ts := by
  blaster (induction: auto) (summaries: [unValueDataInner_ascending, get?_below]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unValueDataOuter_ascending (prev : Option ByteString) (d : List (Data × Data)) (w : Value) :
    unValueDataOuter prev d = .ok w → ascending prev w = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unValueDataOuter_inners (prev : Option ByteString) (d : List (Data × Data)) (w : Value) :
    unValueDataOuter prev d = .ok w → innersAscending w = true := by
  blaster (induction: auto) (summaries: [unValueDataInner_ascending]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unValueDataOuter_lookup (prev : Option ByteString) (c t : ByteString) (d : List (Data × Data)) (w : Value) :
    unValueDataOuter prev d = .ok w → lookupCoin c t w = dataQuantity c t d := by
  blaster (induction: auto)
    (summaries: [unValueDataInner_getD, unValueDataOuter_ascending, lookupCoin_cons, get?_belowV])
    (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem findToken_tokensToData (prev : Option ByteString) (t : ByteString) (inner : Tokens) :
    ascending prev inner = true → findToken t (tokensToData inner) = AList.getD t inner 0 := by
  blaster (induction: auto) (summaries: [get?_below]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem dataQuantity_valueToDataEntries (prev : Option ByteString) (c t : ByteString) (w : Value) :
    ascending prev w = true → innersAscending w = true →
    dataQuantity c t (valueToDataEntries w) = lookupCoin c t w := by
  blaster (induction: auto) (summaries: [findToken_tokensToData, lookupCoin_cons, get?_belowV]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unionValue_lookup (c t : ByteString) (a b r : Value) :
    ascending none a = true → innersAscending a = true →
    ascending none b = true → innersAscending b = true →
    unionValue a b = .ok r → lookupCoin c t r = lookupCoin c t a + lookupCoin c t b := by
  blaster (induction: auto) (summaries: [unionOuter_lookup]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unionValue_ascending (a b r : Value) :
    ascending none a = true → ascending none b = true →
    unionValue a b = .ok r → ascending none r = true := by
  blaster (induction: auto) (summaries: [unionOuter_ascending]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unionValue_inners (a b r : Value) :
    innersAscending a = true → innersAscending b = true →
    unionValue a b = .ok r → innersAscending r = true := by
  blaster (induction: auto) (summaries: [unionOuter_inners]) (timeout: 20) (gen-cex: 0)

/-- The quantity of `(cur, tok)` in `Data` holding a nested map (0 otherwise). -/
def dataQuantityOf (cur tok : ByteString) : Data → Integer
  | .Map entries => dataQuantity cur tok entries
  | _ => 0

@[blaster_library] theorem unValueData_lookup (c t : ByteString) (d : Data) (w : Value) :
    unValueData d = .ok w → lookupCoin c t w = dataQuantityOf c t d := by
  blaster (induction: auto) (summaries: [unValueDataOuter_lookup]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unValueData_ascending (d : Data) (w : Value) :
    unValueData d = .ok w → ascending none w = true := by
  blaster (induction: auto) (summaries: [unValueDataOuter_ascending]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem unValueData_inners (d : Data) (w : Value) :
    unValueData d = .ok w → innersAscending w = true := by
  blaster (induction: auto) (summaries: [unValueDataOuter_inners]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem valueData_lookup (c t : ByteString) (w : Value) (d : Data) :
    ascending none w = true → innersAscending w = true →
    valueData w = .ok d → dataQuantityOf c t d = lookupCoin c t w := by
  blaster (induction: auto) (summaries: [dataQuantity_valueToDataEntries]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem valueData_lookup_map (c t : ByteString) (w : Value) (es : List (Data × Data)) :
    ascending none w = true → innersAscending w = true →
    valueData w = .ok (Data.Map es) → dataQuantity c t es = lookupCoin c t w := by
  blaster (induction: auto) (summaries: [valueData_lookup]) (timeout: 20) (gen-cex: 0)

/-- `unionOuter_lookup` for operands sorted from the start (no lower bound). -/
@[blaster_library] theorem unionOuter_lookup_none (c t : ByteString) (acc b r : Value) :
    ascending none acc = true → innersAscending acc = true →
    ascending none b = true → innersAscending b = true →
    unionOuter acc b = .ok r →
    lookupCoin c t r = lookupCoin c t acc + lookupCoin c t b := by
  blaster (summaries: [unionOuter_lookup none c t acc b r]) (timeout: 20) (gen-cex: 0)

/-- Every entry of an encoded value carries a map of tokens. -/
def mapEntries : List (Data × Data) → Bool
  | [] => true
  | (_, Data.Map _) :: rest => mapEntries rest
  | _ => false

@[blaster_library] theorem mapEntries_tail (e : Data × Data) (es : List (Data × Data)) :
    mapEntries (e :: es) = true → mapEntries es = true := by
  blaster (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem mapEntries_valueToDataEntries (w : Value) :
    mapEntries (valueToDataEntries w) = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem valueData_entries (w : Value) (es : List (Data × Data)) :
    valueData w = .ok (Data.Map es) → es = valueToDataEntries w := by
  blaster (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem dataQuantity_cons_skip (k v : Data) (es : List (Data × Data)) (c t : ByteString) :
    mapEntries ((k, v) :: es) = true → (Data.B c == k) = false →
      dataQuantity c t ((k, v) :: es) = dataQuantity c t es := by
  blaster (timeout: 20) (gen-cex: 0)

end BlasterFacts

end Internal

export Internal (ascending innersAscending findToken dataQuantity dataQuantityOf)

end PlutusCore.Value
