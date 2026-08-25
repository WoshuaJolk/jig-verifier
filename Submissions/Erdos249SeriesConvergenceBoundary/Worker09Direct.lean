import Mathlib

namespace Submissions.Erdos249SeriesConvergenceBoundary.Worker09Direct

noncomputable def term (n : ℕ) : ℝ :=
  (Nat.totient n : ℝ) / (2 : ℝ) ^ n

theorem proof : Summable term ∧ term 0 = 0 := by
  constructor
  · have hmajor :
        Summable (fun n : ℕ =>
          ‖((n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n : ℝ)‖) :=
      summable_norm_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    have hmajor' :
        Summable (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) := by
      simpa [div_eq_mul_inv, ← inv_pow] using hmajor
    apply Summable.of_nonneg_of_le
      (fun n => div_nonneg (Nat.cast_nonneg _) (by positivity))
      (fun n => ?_)
      hmajor'
    gcongr
    exact_mod_cast Nat.totient_le n
  · simp [term, Nat.totient_zero]

end Submissions.Erdos249SeriesConvergenceBoundary.Worker09Direct
