import Mathlib

/- BEGIN bundled local module RootDegreeMoment -/


namespace ColeskiRootDegreeMoment
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem pair_integrable (W : Ω × Ω → ℝ) (hm : Measurable W)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ W p ∧ W p ≤ 1) : Integrable W (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [hb] with p hp
  simpa only [Real.norm_eq_abs,abs_of_nonneg hp.1] using hp.2

theorem centered (W : Ω × Ω → ℝ) (hm : Measurable W)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ W p ∧ W p ≤ 1)
    (hd : ∀ᵐ x ∂μ, (∫ y, W (x,y) ∂μ) = (1/6 : ℝ)) :
    ∀ᵐ x ∂μ, (∫ y, 6 * W (x,y) - 1 ∂μ) = 0 := by
  filter_upwards [(pair_integrable μ W hm hb).prod_right_ae,hd] with x hi hd
  rw [integral_sub (hi.const_mul 6) (integrable_const 1),integral_const_mul,hd]
  norm_num

theorem deleted_vertex_integral (W : Ω × Ω → ℝ) (hm : Measurable W)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ W p ∧ W p ≤ 1)
    (hd : ∀ᵐ x ∂μ, (∫ y, W (x,y) ∂μ) = (1/6 : ℝ))
    (m : Fin 5) (F : (Fin 5 → Ω) → ℝ) :
    (∫ x, ∫ y, F x * (6 * W (x m,y) - 1) ∂μ
      ∂Measure.pi (fun _ : Fin 5 => μ)) = 0 := by
  apply integral_eq_zero_of_ae
  have hp := measurePreserving_eval (fun _ : Fin 5 => μ) m
  have hh : ∀ᵐ x ∂Measure.pi (fun _ : Fin 5 => μ),
      (∫ y, 6 * W (x m,y) - 1 ∂μ) = 0 := by
    apply ae_of_ae_map (p := fun z => (∫ y, 6 * W (z,y) - 1 ∂μ) = 0)
      hp.measurable.aemeasurable
    rw [hp.map_eq]
    exact centered μ W hm hb hd
  filter_upwards [hh] with x hx
  rw [integral_const_mul,hx,mul_zero]
  rfl

end ColeskiRootDegreeMoment
#print axioms ColeskiRootDegreeMoment.centered
#print axioms ColeskiRootDegreeMoment.deleted_vertex_integral

/- END bundled local module RootDegreeMoment -/
