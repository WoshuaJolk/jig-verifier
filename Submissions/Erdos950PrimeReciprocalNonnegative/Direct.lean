import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos950PrimeReciprocalNonnegative.Direct

noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter Nat.Prime,
    (1 : ℝ) / (n - p : ℝ)

theorem proof : ∀ n : ℕ, 0 ≤ f n := by
  intro n
  unfold f
  apply Finset.sum_nonneg
  intro p hp
  apply div_nonneg
  · norm_num
  · have hpn : p ≤ n :=
      Nat.le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    exact sub_nonneg.mpr (by exact_mod_cast hpn)

end Submissions.Erdos950PrimeReciprocalNonnegative.Direct
