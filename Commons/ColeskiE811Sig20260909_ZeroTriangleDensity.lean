import Mathlib

/- BEGIN bundled local module ZeroTriangleDensity -/


namespace ColeskiZeroTriangleDensity
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

theorem ae_zero_of_nested_integral
    (f : Ω → Ω → Ω → ℝ)
    (integrable : Integrable (fun p : Ω × Ω × Ω => f p.1 p.2.1 p.2.2)
      (μ.prod (μ.prod μ)))
    (nonnegative : ∀ᵐ p ∂μ.prod (μ.prod μ), 0 ≤ f p.1 p.2.1 p.2.2)
    (zero : (∫ x, ∫ y, ∫ z, f x y z ∂μ ∂μ ∂μ) = 0) :
    ∀ᵐ p ∂μ.prod (μ.prod μ), f p.1 p.2.1 p.2.2 = 0 := by
  apply (integral_eq_zero_iff_of_nonneg_ae nonnegative integrable).mp
  rw [MeasureTheory.integral_prod _ integrable]
  calc
    _ = ∫ x, ∫ y, ∫ z, f x y z ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [integrable.prod_right_ae] with x hx
      exact MeasureTheory.integral_prod _ hx
    _ = 0 := zero

theorem ae_zero_factor
    (a b c : Ω → Ω → Ω → ℝ)
    (integrable : Integrable (fun p : Ω × Ω × Ω =>
      a p.1 p.2.1 p.2.2 * b p.1 p.2.1 p.2.2 * c p.1 p.2.1 p.2.2)
      (μ.prod (μ.prod μ)))
    (nonnegative : ∀ᵐ p ∂μ.prod (μ.prod μ),
      0 ≤ a p.1 p.2.1 p.2.2 * b p.1 p.2.1 p.2.2 * c p.1 p.2.1 p.2.2)
    (zero : (∫ x, ∫ y, ∫ z, a x y z * b x y z * c x y z ∂μ ∂μ ∂μ) = 0) :
    ∀ᵐ p ∂μ.prod (μ.prod μ),
      a p.1 p.2.1 p.2.2 = 0 ∨ b p.1 p.2.1 p.2.2 = 0 ∨ c p.1 p.2.1 p.2.2 = 0 := by
  filter_upwards [ae_zero_of_nested_integral μ _ integrable nonnegative zero] with p hp
  simpa only [mul_eq_zero, or_assoc] using hp

end ColeskiZeroTriangleDensity
#print axioms ColeskiZeroTriangleDensity.ae_zero_of_nested_integral
#print axioms ColeskiZeroTriangleDensity.ae_zero_factor

/- END bundled local module ZeroTriangleDensity -/
