import Commons.ColeskiE811Sig20260909_ProductColorLaw

/- BEGIN bundled local module IntegratedColorLaw -/


namespace ColeskiIntegratedColorLaw
open MeasureTheory Finset
variable {Ω E C : Type*} [MeasurableSpace Ω] [Fintype E] [Fintype C]
    [DecidableEq E] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def law (w : Ω → E → C → ℝ) (a : E → C) : ℝ :=
  ∫ x, ColeskiProductColorLaw.mass (w x) a ∂μ

theorem integrable_mass (w : Ω → E → C → ℝ)
    (measurable : ∀ e c, Measurable (fun x => w x e c))
    (bounds : ∀ᵐ x ∂μ, ∀ e c, 0 ≤ w x e c ∧ w x e c ≤ 1)
    (a : E → C) : Integrable (fun x => ColeskiProductColorLaw.mass (w x) a) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · unfold ColeskiProductColorLaw.mass
    exact (Finset.measurable_prod _ (fun e _ => measurable e (a e))).aestronglyMeasurable
  · filter_upwards [bounds] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (ColeskiProductColorLaw.nonnegative _ (fun e c => (hx e c).1) a)]
    exact Finset.prod_le_one (fun e _ => (hx e (a e)).1) (fun e _ => (hx e (a e)).2)

theorem nonnegative (w : Ω → E → C → ℝ)
    (h : ∀ᵐ x ∂μ, ∀ e c, 0 ≤ w x e c) (a : E → C) : 0 ≤ law μ w a := by
  apply integral_nonneg_of_ae
  filter_upwards [h] with x hx
  exact ColeskiProductColorLaw.nonnegative _ hx a

theorem normalized (w : Ω → E → C → ℝ)
    (measurable : ∀ e c, Measurable (fun x => w x e c))
    (bounds : ∀ᵐ x ∂μ, ∀ e c, 0 ≤ w x e c ∧ w x e c ≤ 1)
    (total : ∀ᵐ x ∂μ, ∀ e, ∑ c, w x e c = 1) :
    ∑ a : E → C, law μ w a = 1 := by
  unfold law
  rw [← integral_finset_sum _ (fun a _ => integrable_mass μ w measurable bounds a)]
  calc
    _ = ∫ _ : Ω, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [total] with x hx
      exact ColeskiProductColorLaw.normalized _ hx
    _ = 1 := by simp

theorem zero_of_ae_zero_factor (w : Ω → E → C → ℝ) (a : E → C)
    (h : ∀ᵐ x ∂μ, ∃ e, w x e (a e) = 0) : law μ w a = 0 := by
  unfold law
  apply integral_eq_zero_of_ae
  filter_upwards [h] with x hx
  obtain ⟨e,he⟩ := hx
  exact ColeskiProductColorLaw.zero_of_zero_factor _ a e he

end ColeskiIntegratedColorLaw
#print axioms ColeskiIntegratedColorLaw.integrable_mass
#print axioms ColeskiIntegratedColorLaw.normalized
#print axioms ColeskiIntegratedColorLaw.zero_of_ae_zero_factor

/- END bundled local module IntegratedColorLaw -/
