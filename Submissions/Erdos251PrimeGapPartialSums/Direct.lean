import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

namespace Submissions.Erdos251PrimeGapPartialSums.Direct

noncomputable abbrev p (n : ℕ) : ℝ := Nat.nth Nat.Prime n

theorem proof :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range (N + 1), p n / 2 ^ n) =
        4 + (∑ n ∈ Finset.range N, (p (n + 1) - p n) / 2 ^ n) -
          p N / 2 ^ N := by
  intro N
  induction N with
  | zero => norm_num [p]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      rw [pow_succ]
      ring

end Submissions.Erdos251PrimeGapPartialSums.Direct
