/- Execution budget for UPLC evaluation, tracking CPU and Memory resources
-/

namespace PlutusCore.UPLC.ExBudget

-- CPU Units
-- Structure just in case in the future we need more complex domains for value analysis
structure ExCPU where
  unExCPU : Nat
deriving Repr, Inhabited, DecidableEq, BEq

instance : LawfulBEq ExCPU where
  eq_of_beq {a b} h := by cases a; cases b; simp_all [BEq.beq, instBEqExCPU.beq]
  rfl {a} := by cases a; simp [BEq.beq, instBEqExCPU.beq]

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

instance : LawfulBEq ExMemory where
  eq_of_beq {a b} h := by cases a; cases b; simp_all [BEq.beq, instBEqExMemory.beq]
  rfl {a} := by cases a; simp [BEq.beq, instBEqExMemory.beq]

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

instance : LawfulBEq ExBudget where
  eq_of_beq {a b} h := by
    cases a; cases b
    change instBEqExBudget.beq _ _ = true at h
    simp_all [instBEqExBudget.beq]
  rfl {a} := by
    cases a
    change instBEqExBudget.beq _ _ = true
    simp [instBEqExBudget.beq]

namespace ExBudget

  def add (a b : ExBudget) : ExBudget :=
    ⟨a.exBudgetCPU + b.exBudgetCPU, a.exBudgetMemory + b.exBudgetMemory⟩

  def subtract (a b : ExBudget) : ExBudget :=
    ⟨a.exBudgetCPU - b.exBudgetCPU, a.exBudgetMemory - b.exBudgetMemory⟩

  def zero : ExBudget := ⟨0, 0⟩

  instance : Add ExBudget := ⟨add⟩
  instance : Sub ExBudget := ⟨subtract⟩

  -- Can we afford a given cost
  def canAfford (budget : ExBudget) (cost : ExBudget) : Bool :=
    budget.exBudgetCPU.unExCPU >= cost.exBudgetCPU.unExCPU &&
    budget.exBudgetMemory.unExMemory >= cost.exBudgetMemory.unExMemory

  -- Spend cost from budget
  -- Assumes that the cost can be afforded, should be checked with `canAfford` before calling
  def spend (budget : ExBudget) (cost : ExBudget) : ExBudget :=
    budget - cost

  -- Componentwise order
  instance : LE ExBudget :=
    ⟨λ a b => a.exBudgetCPU.unExCPU ≤ b.exBudgetCPU.unExCPU ∧
              a.exBudgetMemory.unExMemory ≤ b.exBudgetMemory.unExMemory⟩

  /-! ### Arithmetic, componentwise -/

  @[simp] theorem add_cpu (a b : ExBudget) :
      (a + b).exBudgetCPU.unExCPU = a.exBudgetCPU.unExCPU + b.exBudgetCPU.unExCPU := rfl

  @[simp] theorem add_mem (a b : ExBudget) :
      (a + b).exBudgetMemory.unExMemory = a.exBudgetMemory.unExMemory + b.exBudgetMemory.unExMemory := rfl

  @[simp] theorem sub_cpu (a b : ExBudget) :
      (a - b).exBudgetCPU.unExCPU = a.exBudgetCPU.unExCPU - b.exBudgetCPU.unExCPU := rfl

  @[simp] theorem sub_mem (a b : ExBudget) :
      (a - b).exBudgetMemory.unExMemory = a.exBudgetMemory.unExMemory - b.exBudgetMemory.unExMemory := rfl

  @[simp] theorem zero_cpu : ExBudget.zero.exBudgetCPU.unExCPU = 0 := rfl

  @[simp] theorem zero_mem : ExBudget.zero.exBudgetMemory.unExMemory = 0 := rfl

  theorem le_def (a b : ExBudget) :
      a ≤ b ↔ a.exBudgetCPU.unExCPU ≤ b.exBudgetCPU.unExCPU ∧
              a.exBudgetMemory.unExMemory ≤ b.exBudgetMemory.unExMemory := Iff.rfl

  @[simp] theorem canAfford_eq_true_iff (b c : ExBudget) :
      b.canAfford c = true ↔ c.exBudgetCPU.unExCPU ≤ b.exBudgetCPU.unExCPU ∧
                             c.exBudgetMemory.unExMemory ≤ b.exBudgetMemory.unExMemory := by
    simp [canAfford]

  theorem ext {a b : ExBudget}
      (hcpu : a.exBudgetCPU.unExCPU = b.exBudgetCPU.unExCPU)
      (hmem : a.exBudgetMemory.unExMemory = b.exBudgetMemory.unExMemory) : a = b := by
    cases a with | mk c m => cases b with | mk c' m' =>
    cases c; cases m; cases c'; cases m'
    simp_all

  theorem add_assoc (a b c : ExBudget) : a + b + c = a + (b + c) := by
    apply ext <;> simp only [add_cpu, add_mem] <;> omega

  @[simp] theorem zero_add (a : ExBudget) : ExBudget.zero + a = a := by
    apply ext <;> simp

  @[simp] theorem add_zero (a : ExBudget) : a + ExBudget.zero = a := by
    apply ext <;> simp

  theorem le_add_right (a b : ExBudget) : a ≤ a + b := by
    simp only [le_def, add_cpu, add_mem]; omega

  theorem canAfford_mono {a b c : ExBudget} (hab : a ≤ b) (h : a.canAfford c = true) :
      b.canAfford c = true := by
    simp only [canAfford_eq_true_iff, le_def] at *; omega

  end ExBudget
end PlutusCore.UPLC.ExBudget
