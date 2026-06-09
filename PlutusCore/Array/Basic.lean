namespace PlutusCore.Array

namespace Internal

def lengthOfArray {α} : List α → Nat    := List.length
def listToArray   {α} : List α → List α := id

def indexArray {α} (a : List α) (n : Nat) : Option α := a[n]?

end Internal

export Internal
  (
    -- functions
    lengthOfArray
    listToArray
    indexArray
  )

end PlutusCore.Array
