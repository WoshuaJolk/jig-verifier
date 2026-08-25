import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos882SubsetSumRangeBound.Direct

open Finset

theorem proof :
    ∀ n : ℕ, ∀ A B : Finset ℕ,
      A ⊆ Icc 1 n → B ⊆ A →
      B.sum id ≤ A.card * n := by
  intro n A B hA hB
  calc
    B.sum id ≤ B.card * n := by
      apply Finset.sum_le_card_nsmul
      intro b hb
      exact (Finset.mem_Icc.mp (hA (hB hb))).2
    _ ≤ A.card * n := by
      exact Nat.mul_le_mul_right n (Finset.card_le_card hB)

end Submissions.Erdos882SubsetSumRangeBound.Direct
