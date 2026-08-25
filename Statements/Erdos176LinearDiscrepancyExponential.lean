import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos176LinearDiscrepancyExponential

open scoped BigOperators

/-- Every ±1 coloring of `[0,N)` has a `k`-term AP of discrepancy at least `l`. -/
def ForcesDiscrepancy (k N : ℕ) (l : ℝ) : Prop :=
  ∀ f : Fin N → ℤ,
    (∀ x, f x = -1 ∨ f x = 1) →
      ∃ a d : ℕ, 0 < d ∧
        ∃ hlast : a + (k - 1) * d < N,
          l ≤ ((|(∑ j : Fin k,
            f ⟨a + j.val * d,
              lt_of_le_of_lt
                (Nat.add_le_add_left
                  (Nat.mul_le_mul_right d (Nat.le_pred_of_lt j.isLt)) a)
                hlast⟩ : ℤ)| : ℤ) : ℝ)

/-- The unresolved linear-discrepancy part of Erdős problem 176. -/
abbrev statement : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 →
    ∃ C : ℝ, 1 < C ∧
      ∀ k : ℕ, 1 ≤ k →
        ForcesDiscrepancy k ⌊C ^ k⌋₊ (c * k)

theorem target : statement := sorry

end Statements.Erdos176LinearDiscrepancyExponential
