import Commons.ColeskiE811Sig20260909_SampledCoordinates
import Commons.ColeskiE811Sig20260909_IntegratedColorLaw

/- BEGIN bundled local module SixVertexLaw -/


namespace ColeskiSixVertexLaw
open MeasureTheory
abbrev Edge := {p : Fin 6 × Fin 6 // p.1 < p.2}

def endpoints (e : Edge) : Fin 2 ↪ Fin 6 where
  toFun := ![e.val.1,e.val.2]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals have he := e.property
    all_goals omega

variable {Ω : Type*} [MeasurableSpace Ω]

def weights (W : Fin 6 → Ω × Ω → ℝ) (x : Fin 6 → Ω) (e : Edge) (c : Fin 6) : ℝ :=
  W c (x e.val.1,x e.val.2)

theorem measurable_weights (W : Fin 6 → Ω × Ω → ℝ)
    (h : ∀ c, Measurable (W c)) (e : Edge) (c : Fin 6) :
    Measurable (fun x => weights W x e c) := by
  exact (h c).comp ((measurable_pi_apply e.val.1).prodMk (measurable_pi_apply e.val.2))

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounds (W : Fin 6 → Ω × Ω → ℝ)
    (h : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin 6 => μ), ∀ e c,
      0 ≤ weights W x e c ∧ weights W x e c ≤ 1 := by
  rw [ae_all_iff]
  intro e
  rw [ae_all_iff]
  intro c
  exact ColeskiSampledCoordinates.pair_ae_pullback μ (endpoints e) _ (h c)

theorem totals (W : Fin 6 → Ω × Ω → ℝ)
    (h : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin 6 => μ), ∀ e, ∑ c, weights W x e c = 1 := by
  rw [ae_all_iff]
  intro e
  exact ColeskiSampledCoordinates.pair_ae_pullback μ (endpoints e) _ h

noncomputable def mass (W : Fin 6 → Ω × Ω → ℝ) (a : Edge → Fin 6) : ℝ :=
  ColeskiIntegratedColorLaw.law (Measure.pi (fun _ : Fin 6 => μ)) (weights W) a

theorem mass_nonnegative (W : Fin 6 → Ω × Ω → ℝ)
    (h : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) (a : Edge → Fin 6) :
    0 ≤ mass μ W a := by
  apply ColeskiIntegratedColorLaw.nonnegative
  filter_upwards [bounds μ W h] with x hx
  exact fun e c => (hx e c).1

theorem mass_normalized (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1) :
    ∑ a : Edge → Fin 6, mass μ W a = 1 := by
  exact ColeskiIntegratedColorLaw.normalized _ _ (measurable_weights W hm)
    (bounds μ W hb) (totals μ W ht)

end ColeskiSixVertexLaw
#print axioms ColeskiSixVertexLaw.mass_nonnegative
#print axioms ColeskiSixVertexLaw.mass_normalized

/- END bundled local module SixVertexLaw -/
