import Mathlib.Analysis.PSeries
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos12LocalBoundsInsufficient.EvenQuotients

/-- The even quotient sequence in the `1 mod 20` progression saturates every
recursive-anchor half-window bound, yet its translated reciprocal series
diverges.  Thus the local cardinality bounds alone cannot yield global decay. -/
theorem proof :
    (∀ n k : ℕ,
      (2 * n < 2 * k ∧
          2 * k < 2 * n + (1 + 20 * (2 * n))) ↔
        k ∈ Finset.Ioc n (21 * n)) ∧
    (∀ n : ℕ,
      (Finset.Ioc n (21 * n)).card =
        (1 + 20 * (2 * n)) / 2) ∧
    ¬ Summable (fun n : ℕ => (1 : ℝ) / (1 + 40 * n)) := by
  constructor
  · intro n k
    simp only [Finset.mem_Ioc]
    omega
  constructor
  · intro n
    simp
    omega
  · intro hsum
    have hsmall :
        Summable (fun n : ℕ => (1 : ℝ) / (41 * (n + 1))) := by
      apply hsum.of_nonneg_of_le
      · intro n
        positivity
      · intro n
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith
    have hshift : Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
      have hscaled :
          Summable (fun n : ℕ =>
            (41 : ℝ) * ((1 : ℝ) / (41 * (n + 1)))) :=
        hsmall.mul_left 41
      apply hscaled.congr
      intro n
      field_simp
    have hshift' :
        Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
      simpa using hshift
    exact (mt (summable_nat_add_iff 1).1
      Real.not_summable_one_div_natCast) hshift'

end Submissions.Erdos12LocalBoundsInsufficient.EvenQuotients
