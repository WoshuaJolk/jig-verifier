import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic

namespace Statements.Erdos176OnePointDiscrepancy

open scoped BigOperators

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

/-- A one-point interval forces discrepancy one on its one-term AP. -/
abbrev statement : Prop := ForcesDiscrepancy 1 1 1

theorem target : statement := sorry

end Statements.Erdos176OnePointDiscrepancy
