import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos176OnePointDiscrepancy.Direct

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

theorem proof : ForcesDiscrepancy 1 1 1 := by
  intro f hf
  refine ⟨0, 1, by norm_num, ?_⟩
  refine ⟨by norm_num, ?_⟩
  have h0 := hf (0 : Fin 1)
  rcases h0 with h0 | h0 <;> simp [h0]

end Submissions.Erdos176OnePointDiscrepancy.Direct
