import Mathlib.Analysis.PSeries

namespace Submissions.Erdos12QuadraticGrowth.QuadraticComparison

theorem proof :
    ∀ u : ℕ → ℕ,
      StrictMono u →
      (∀ i j k : ℕ, i < j → i < k → u i ∣ u j + u k → j = k) →
      (∀ n : ℕ, (n + 1) ^ 2 ≤ u n) →
      Summable (fun n : ℕ => (1 : ℝ) / (u n : ℝ)) := by
  intro u _hStrict _hPropertyP hgrowth
  have hpseries : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1) ^ 2 : ℕ) : ℝ)) := by
    simpa [Nat.cast_pow] using
      ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)))
  apply hpseries.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast hgrowth n

end Submissions.Erdos12QuadraticGrowth.QuadraticComparison
