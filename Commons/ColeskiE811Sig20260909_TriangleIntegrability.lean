import Mathlib

/- BEGIN bundled local module TriangleIntegrability -/


namespace ColeskiTriangleIntegrability
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem xy_preserving : MeasurePreserving (fun p : Ω × Ω × Ω => (p.1,p.2.1))
    (μ.prod (μ.prod μ)) (μ.prod μ) := by
  exact (MeasurePreserving.id μ).prod measurePreserving_fst

theorem zx_preserving : MeasurePreserving (fun p : Ω × Ω × Ω => (p.2.2,p.1))
    (μ.prod (μ.prod μ)) (μ.prod μ) := by
  exact (Measure.measurePreserving_swap (μ := μ) (ν := μ)).comp
    ((MeasurePreserving.id μ).prod measurePreserving_snd)

theorem bounds (A B C : Ω × Ω → ℝ)
    (ha : ∀ᵐ p ∂μ.prod μ, 0 ≤ A p ∧ A p ≤ 1)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ B p ∧ B p ≤ 1)
    (hc : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1) :
    ∀ᵐ p ∂μ.prod (μ.prod μ),
      0 ≤ A (p.1,p.2.1) * B p.2 * C (p.2.2,p.1) ∧
      A (p.1,p.2.1) * B p.2 * C (p.2.2,p.1) ≤ 1 := by
  have hA : ∀ᵐ p ∂μ.prod (μ.prod μ), 0 ≤ A (p.1,p.2.1) ∧ A (p.1,p.2.1) ≤ 1 := by
    apply ae_of_ae_map (p := fun q => 0 ≤ A q ∧ A q ≤ 1)
      (xy_preserving μ).measurable.aemeasurable
    rwa [(xy_preserving μ).map_eq]
  have hB : ∀ᵐ p ∂μ.prod (μ.prod μ), 0 ≤ B p.2 ∧ B p.2 ≤ 1 := by
    apply ae_of_ae_map (p := fun q => 0 ≤ B q ∧ B q ≤ 1)
      (measurePreserving_snd (μ := μ) (ν := μ.prod μ)).measurable.aemeasurable
    rwa [measurePreserving_snd.map_eq]
  have hC : ∀ᵐ p ∂μ.prod (μ.prod μ), 0 ≤ C (p.2.2,p.1) ∧ C (p.2.2,p.1) ≤ 1 := by
    apply ae_of_ae_map (p := fun q => 0 ≤ C q ∧ C q ≤ 1)
      (zx_preserving μ).measurable.aemeasurable
    rwa [(zx_preserving μ).map_eq]
  filter_upwards [hA,hB,hC] with p hA hB hC
  constructor
  · exact mul_nonneg (mul_nonneg hA.1 hB.1) hC.1
  · calc
      _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul hA.2 hB.2 hB.1 (by norm_num)) hC.2 hC.1 (by norm_num)
      _ = 1 := by norm_num

theorem integrable (A B C : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (ha : ∀ᵐ p ∂μ.prod μ, 0 ≤ A p ∧ A p ≤ 1)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ B p ∧ B p ≤ 1)
    (hc : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1) :
    Integrable (fun p : Ω × Ω × Ω => A (p.1,p.2.1) * B p.2 * C (p.2.2,p.1))
      (μ.prod (μ.prod μ)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [bounds μ A B C ha hb hc] with p hp
    simpa only [Real.norm_eq_abs,abs_of_nonneg hp.1] using hp.2

end ColeskiTriangleIntegrability
#print axioms ColeskiTriangleIntegrability.bounds
#print axioms ColeskiTriangleIntegrability.integrable

/- END bundled local module TriangleIntegrability -/
