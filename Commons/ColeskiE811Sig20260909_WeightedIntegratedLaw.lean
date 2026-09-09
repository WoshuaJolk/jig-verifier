import Commons.ColeskiE811Sig20260909_IntegratedColorLaw

/- BEGIN bundled local module WeightedIntegratedLaw -/


namespace ColeskiWeightedIntegratedLaw
open MeasureTheory
variable {Ω E C : Type*} [MeasurableSpace Ω] [Fintype E] [Fintype C] [DecidableEq E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem expectation (w : Ω → E → C → ℝ)
    (hm : ∀ e c, Measurable (fun x => w x e c))
    (hb : ∀ᵐ x ∂μ, ∀ e c, 0 ≤ w x e c ∧ w x e c ≤ 1)
    (q : (E → C) → ℝ) :
    (∑ a : E → C, ColeskiIntegratedColorLaw.law μ w a * q a) =
      ∫ x, ∑ a : E → C, ColeskiProductColorLaw.mass (w x) a * q a ∂μ := by
  unfold ColeskiIntegratedColorLaw.law
  simp_rw [← integral_mul_const]
  exact (integral_finsetSum _ (fun a _ =>
    (ColeskiIntegratedColorLaw.integrable_mass μ w hm hb a).mul_const (q a))).symm

theorem integrable_expectation (w : Ω → E → C → ℝ)
    (hm : ∀ e c, Measurable (fun x => w x e c))
    (hb : ∀ᵐ x ∂μ, ∀ e c, 0 ≤ w x e c ∧ w x e c ≤ 1)
    (q : (E → C) → ℝ) :
    Integrable (fun x => ∑ a : E → C, ColeskiProductColorLaw.mass (w x) a * q a) μ := by
  exact integrable_finset_sum _ (fun a _ =>
    (ColeskiIntegratedColorLaw.integrable_mass μ w hm hb a).mul_const (q a))

end ColeskiWeightedIntegratedLaw
#print axioms ColeskiWeightedIntegratedLaw.expectation
#print axioms ColeskiWeightedIntegratedLaw.integrable_expectation

/- END bundled local module WeightedIntegratedLaw -/
