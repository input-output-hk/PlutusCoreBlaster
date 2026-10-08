import PlutusCoreFacts
import FactTests.Support

open PlutusCore.ByteString (ByteString)
open PlutusCore.Value PlutusCore.Value.Internal

-- Clients can apply a published summary without unfolding a recursive value walk.
example (c t : ByteString) (a b r : Value)
    (ha : ascending none a = true) (hia : innersAscending a = true)
    (hb : ascending none b = true) (hib : innersAscending b = true)
    (hu : unionValue a b = .ok r) :
    lookupCoin c t r = lookupCoin c t a + lookupCoin c t b := by
  blaster (induction: auto) (summaries: [unionValue_lookup]) (timeout: 20) (gen-cex: 0)

-- Sortedness is required: insertion does not repair an arbitrary unsorted map.
#reject "could not prove the goal" in
example (k : ByteString) (v : Int) (xs : Tokens) :
    ascending none (AList.insert k v xs) = true := by
  blaster (induction: auto) (summaries: [ascending_insert]) (timeout: 10) (gen-cex: 0)

-- Decoding succeeds only on the expected Data shape.
example : unValueData (.I 4) = .error "unValueData: non-Map constructor" := by rfl
