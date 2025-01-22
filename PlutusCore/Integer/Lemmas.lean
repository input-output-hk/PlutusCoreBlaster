import PlutusCore.Integer.Basic

namespace PlutusCore.Integer

/-! ## Theorems on Integer representation and builtin functions. -/

@[simp] theorem addInteger_rfl (x y : Integer) : addInteger x y = Int.add x y := rfl
@[simp] theorem subtractInteger_rfl (x y : Integer) : subtractInteger x y = Int.sub x y := rfl
@[simp] theorem multiplyInteger_rfl (x y : Integer) : multiplyInteger x y = Int.mul x y := rfl

@[simp] theorem divideInteger_rfl (x y : Integer) :
  divideInteger x y = if y != 0 then pure (Int.fdiv x y) else throw "divideInteger: division by zero" := rfl

@[simp] theorem divideInteger_zero (x : Integer) :
  divideInteger x 0 = throw "divideInteger: division by zero" := rfl

@[simp] theorem modInteger_rfl (x y : Integer) :
  modInteger x y = if y != 0 then pure (Int.fmod x y) else throw "modInteger: division by zero" := rfl

@[simp] theorem modInteger_zero (x : Integer) :
  modInteger x 0 = throw "modInteger: division by zero" := rfl

@[simp] theorem quotientInteger_rfl (x y : Integer) :
  quotientInteger x y = if y != 0 then pure (Int.div x y) else throw "quotientInteger: division by zero" := rfl

@[simp] theorem quotientInteger_zero (x : Integer) :
  quotientInteger x 0 = throw "quotientInteger: division by zero" := rfl

@[simp] theorem remainderInteger_rfl (x y : Integer) :
  remainderInteger x y = if y != 0 then pure (Int.mod x y) else throw "remainderInteger: division by zero" := rfl

@[simp] theorem remainderInteger_zero (x : Integer) :
  remainderInteger x 0 = throw "remainderInteger: division by zero" := rfl

@[simp] theorem equalsInteger_rfl (x y : Integer) : equalsInteger x y = (x == y) := rfl
@[simp] theorem equalsInteger_iff_eq (x y : Integer) : equalsInteger x y ↔ x = y := by simp

@[simp] theorem lessThanInteger_rfl (x y : Integer) : lessThanInteger x y = (x < y) :=
  by simp [lessThanInteger]

@[simp] theorem lessThanEqualsInteger_rfl (x y : Integer) : lessThanEqualsInteger x y = (x ≤ y) :=
  by simp [lessThanEqualsInteger]

end PlutusCore.Integer
