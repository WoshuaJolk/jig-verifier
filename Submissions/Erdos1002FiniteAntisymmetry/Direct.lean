import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos1002FiniteAntisymmetry.Direct

open Real Finset

noncomputable def discrepancyAverage (α : ℝ) (n : ℕ) : ℝ :=
  (1 / log n) *
    ∑ k ∈ Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))

theorem proof :
    ∀ α : ℝ, ∀ n : ℕ,
      (∀ k ∈ Icc (1 : ℕ) n, Int.fract (α * k) ≠ 0) →
      discrepancyAverage (1 - α) n = -discrepancyAverage α n := by
  intro α n hα
  unfold discrepancyAverage
  calc
    (1 / log n) *
          ∑ k ∈ Icc (1 : ℕ) n,
            (1 / 2 - Int.fract ((1 - α) * k)) =
        (1 / log n) *
          ∑ k ∈ Icc (1 : ℕ) n,
            -(1 / 2 - Int.fract (α * k)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hfract :
          Int.fract ((1 - α) * (k : ℝ)) =
            1 - Int.fract (α * (k : ℝ)) := by
        rw [show (1 - α) * (k : ℝ) = -(α * (k : ℝ)) + k by ring,
          Int.fract_add_natCast]
        exact Int.fract_neg (hα k hk)
      rw [hfract]
      ring
    _ = -((1 / log n) *
          ∑ k ∈ Icc (1 : ℕ) n,
            (1 / 2 - Int.fract (α * k))) := by
      simp only [Finset.sum_neg_distrib]
      ring

end Submissions.Erdos1002FiniteAntisymmetry.Direct
