import Cryptograph.BLS12_381.Basic

namespace Cryptograph.BLS12_381

open Cryptograph.String
open Cryptograph.BLS12_381.Internal

theorem g1_times_groupOrder : groupOrder * g1 = .infinity := by native_decide
theorem g2_times_groupOrder : groupOrder * g2 = .infinity := by native_decide

theorem Residuals.mkTwo_orders_correctly {α} [LE α] [DecidableLE α] : ∀ (x₁ x₂ y₁ y₂ : α), Residues.mkTwo x₁ x₂ = .two y₁ y₂ → y₁ ≤ y₂ := by
  intros x₁ x₂
  simp [Residues.mkTwo]
  match Hr₁ : decide (x₁ ≤ x₂), Hr₂ : decide (x₂ ≤ x₁) with
  | true , _     => simp at *; intros; assumption
  | false, true  => simp at *; intros; assumption
  | false, false => simp

theorem Fq1.sqrtMod_some_le : ∀ (a x₁ x₂ : Fq1), Fq1.sqrtMod a = .two x₁ x₂ → x₁ ≤ x₂ := by
  intros a x₁ x₂
  simp [Fq1.sqrtMod]; split <;> try simp
  apply Residuals.mkTwo_orders_correctly

end Cryptograph.BLS12_381
