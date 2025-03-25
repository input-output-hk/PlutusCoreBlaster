
namespace PlutusCore.Integer

/-! ## Formalisation for PlutusCore Integer representation and builtin functions. -/

abbrev Integer := Int

/-! ## Builtin Integer functions. -/

namespace PlutusCore.IntegerInternal

def addInteger := Int.add
def subtractInteger := Int.sub
def multiplyInteger := Int.mul

/-- Division truncating towards negative infinity.
    Trigger an error when denominator is zero.
-/
def divideInteger (x : Integer) (y : Integer) : Except String Integer :=
  if y != 0
  then pure (Int.fdiv x y)
  else throw "divideInteger: division by zero"

/-- Modulo truncating towards negative infinity.
    Trigger an error when denominator is zero.
-/
def modInteger (x : Integer) (y : Integer) : Except String Integer :=
  if y != 0
  then pure (Int.fmod x y)
  else throw "modInteger: division by zero"


/-- Division truncating towards zero.
    Trigger an error when denominator is zero.
-/
def quotientInteger (x : Integer) (y : Integer) : Except String Integer :=
  if y != 0
  then pure (Int.tdiv x y)
  else throw "quotientInteger: division by zero"

/-- Modulo truncating towards zero.
    Trigger an error when denominator is zero.
-/
def remainderInteger (x : Integer) (y : Integer) : Except String Integer :=
  if y != 0
  then pure (Int.tmod x y)
  else throw "remainderInteger: division by zero"

def equalsInteger (x : Integer) (y : Integer) : Bool := x == y
def lessThanInteger (x : Integer) (y : Integer) : Bool := x < y
def lessThanEqualsInteger (x : Integer) (y : Integer) : Bool := x ≤ y

end PlutusCore.IntegerInternal

export PlutusCore.IntegerInternal
  (  -- builtin functions
    addInteger
    divideInteger
    equalsInteger
    lessThanInteger
    lessThanEqualsInteger
    modInteger
    multiplyInteger
    quotientInteger
    remainderInteger
    subtractInteger
  )

end PlutusCore.Integer
