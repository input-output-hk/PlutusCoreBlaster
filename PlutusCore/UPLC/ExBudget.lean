/- Execution beudget for UPLC evaluation, tracking CPU and Memory resources
-/

namespace PlutusCore.UPLC.ExBudget

-- CPU Units
-- Structure just in case in the future we need more complex domains for value analysis
structure ExCPU where
  unExCPU : Nat
deriving Repr, Inhabited, DecidableEq, BEq

namespace ExCPU
  def add (a b : ExCPU) : ExCPU :=
    ⟨a.unExCPU + b.unExCPU⟩

  def subtract (a b : ExCPU) : ExCPU :=
    ⟨a.unExCPU - b.unExCPU⟩

  def zero : ExCPU := ⟨0⟩

  instance : Add ExCPU := ⟨add⟩
  instance : Sub ExCPU := ⟨subtract⟩
  instance : OfNat ExCPU n where
    ofNat := ⟨n⟩

end ExCPU

-- Memory Units
-- Structure just in case in the future we need more complex domains for value analysis
structure ExMemory where
  unExMemory : Nat
deriving Repr, Inhabited, DecidableEq, BEq

namespace ExMemory
  def add (a b : ExMemory) : ExMemory :=
    ⟨a.unExMemory + b.unExMemory⟩

  def subtract (a b : ExMemory) : ExMemory :=
    ⟨a.unExMemory - b.unExMemory⟩

  def zero : ExMemory := ⟨0⟩

  instance : Add ExMemory := ⟨add⟩
  instance : Sub ExMemory := ⟨subtract⟩
  instance : OfNat ExMemory n where
    ofNat := ⟨n⟩

end ExMemory

-- Combined execution budget
structure ExBudget where
  exBudgetCPU : ExCPU
  exBudgetMemory : ExMemory
deriving Repr, Inhabited, DecidableEq, BEq

namespace ExBudget

  def add (a b : ExBudget) : ExBudget :=
    ⟨a.exBudgetCPU + b.exBudgetCPU, a.exBudgetMemory + b.exBudgetMemory⟩

  def subtract (a b : ExBudget) : ExBudget :=
    ⟨a.exBudgetCPU - b.exBudgetCPU, a.exBudgetMemory - b.exBudgetMemory⟩

  def zero : ExBudget := ⟨0, 0⟩

  instance : Add ExBudget := ⟨add⟩
  instance : Sub ExBudget := ⟨subtract⟩

  -- Can we afort a given cost
  def canAfford (budget : ExBudget) (cost : ExBudget) : Bool :=
    budget.exBudgetCPU.unExCPU >= cost.exBudgetCPU.unExCPU &&
    budget.exBudgetMemory.unExMemory >= cost.exBudgetMemory.unExMemory

  -- Spend cost from budget
  -- Assumes that the cost can be afforded, should be checked with `canAfford` before calling
  def spend (budget : ExBudget) (cost : ExBudget) : ExBudget :=
    budget - cost

  end ExBudget
end PlutusCore.UPLC.ExBudget
