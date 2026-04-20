namespace PlutusCore.Array

namespace Internal

def lengthOfArray {α} : Array α → Nat     := Array.size   (α := α)
def listToArray   {α} : List α  → Array α := List.toArray (α := α)

def indexArray {α} (a : Array α) (n : Nat) : Option α := a[n]?

end Internal

export Internal
  (
    -- functions
    lengthOfArray
    listToArray
    indexArray
  )

end PlutusCore.Array
