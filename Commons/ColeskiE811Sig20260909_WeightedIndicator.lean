import Mathlib

/- BEGIN bundled local module WeightedIndicator -/

namespace ColeskiWeightedIndicator
open Finset

theorem sum_indicator (w : Fin 6 → ℝ) (c : Fin 6) :
    (∑ a : Fin 6, w a * ((if c = a then (6 : ℝ) else 0) - 1)) =
      6*w c - ∑ a : Fin 6, w a := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp [mul_ite, mul_comm]
end ColeskiWeightedIndicator
#print axioms ColeskiWeightedIndicator.sum_indicator

/- END bundled local module WeightedIndicator -/
