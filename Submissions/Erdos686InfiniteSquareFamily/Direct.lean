import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos686InfiniteSquareFamily.Direct

open scoped BigOperators

theorem proof : ∀ t : ℕ, ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
    ((4 * (2 * t + 3) ^ 2 : ℕ) : ℚ) =
      (∏ i ∈ Finset.Icc 1 k, (m + i)) /
        (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  intro t
  refine ⟨2, by norm_num, t, 4 * t ^ 2 + 12 * t + 7, by nlinarith, ?_⟩
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self,
    Finset.prod_singleton]
  push_cast
  field_simp
  ring

end Submissions.Erdos686InfiniteSquareFamily.Direct
