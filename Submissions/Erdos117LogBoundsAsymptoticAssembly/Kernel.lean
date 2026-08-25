import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter Asymptotics

namespace Submissions.Erdos117LogBoundsAsymptoticAssembly.Kernel

noncomputable def errorScale (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.log ((n : ℝ) + 2) ^ (3 : ℕ)

theorem proof :
    ∀ (h : ℕ → ℕ) (lowerConstant upperConstant : ℝ),
      0 ≤ lowerConstant →
      0 ≤ upperConstant →
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) / 2 - lowerConstant ≤ Real.logb 2 (h n : ℝ)) →
      (∀ᶠ n : ℕ in atTop,
        Real.logb 2 (h n : ℝ) ≤
          (n : ℝ) / 2 + upperConstant * errorScale n) →
      (fun n : ℕ => Real.logb 2 (h n : ℝ) - (n : ℝ) / 2) =O[atTop]
        errorScale := by
  intro h lowerConstant upperConstant hlower hupper hlowerBound hupperBound
  have hscale : ∀ᶠ n : ℕ in atTop, 1 ≤ errorScale n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [Real.one_le_sqrt]
      exact hnReal
    have hx : 0 ≤ (n : ℝ) + 1 := by positivity
    have hfrac :
        (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) / (((n : ℝ) + 1) + 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hlog : 1 ≤ Real.log ((n : ℝ) + 2) := by
      calc
        (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) / (((n : ℝ) + 1) + 2) := hfrac
        _ ≤ Real.log (1 + ((n : ℝ) + 1)) :=
          Real.le_log_one_add_of_nonneg hx
        _ = Real.log ((n : ℝ) + 2) := by ring_nf
    exact one_le_mul_of_one_le_of_one_le hsqrt (one_le_pow₀ hlog)
  refine IsBigO.of_bound (max lowerConstant upperConstant) ?_
  filter_upwards [hlowerBound, hupperBound, hscale] with n hnLower hnUpper hnScale
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hnScale)]
  apply abs_le.mpr
  have hmaxNonneg : 0 ≤ max lowerConstant upperConstant :=
    hlower.trans (le_max_left _ _)
  have hlowerScale :
      lowerConstant ≤ max lowerConstant upperConstant * errorScale n := by
    calc
      lowerConstant ≤ max lowerConstant upperConstant := le_max_left _ _
      _ = max lowerConstant upperConstant * 1 := by ring
      _ ≤ max lowerConstant upperConstant * errorScale n :=
        mul_le_mul_of_nonneg_left hnScale hmaxNonneg
  have hupperScale :
      upperConstant * errorScale n ≤
        max lowerConstant upperConstant * errorScale n :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hnScale)
  constructor
  · have hdifference :
        -lowerConstant ≤ Real.logb 2 (h n : ℝ) - (n : ℝ) / 2 := by
      linarith
    exact (neg_le_neg hlowerScale).trans hdifference
  · have hdifference :
        Real.logb 2 (h n : ℝ) - (n : ℝ) / 2 ≤
          upperConstant * errorScale n := by
      linarith
    exact hdifference.trans hupperScale

end Submissions.Erdos117LogBoundsAsymptoticAssembly.Kernel
