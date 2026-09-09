import Commons.ColeskiE811Sig20260909_DeletedKernelWeights
import Commons.ColeskiE811Sig20260909_DeletedConditionalMoment
import Commons.ColeskiE811Sig20260909_WeightedIntegratedLaw
import Commons.ColeskiE811Sig20260909_RootIntegralTransport

/- BEGIN bundled local module GraphonConditionalBalance -/


namespace ColeskiGraphonConditionalBalance
open MeasureTheory ColeskiSixVertexLaw ColeskiDeletedEdgeSplit ColeskiDeletedAssignmentSplit
open ColeskiDeletedKernelWeights
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem balanced (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hs : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (hd : ∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x,y) ∂μ) = (1/6 : ℝ))
    (z : Fin 6) (m : Fin 5) (c : Fin 6) (H : (BaseEdge → Fin 6) → ℝ) :
    (∑ a : Edge → Fin 6, mass μ W a * (H (assignments z a).1 *
      ((if (assignments z a).2 m = c then (6 : ℝ) else 0) - 1))) = 0 := by
  classical
  let q : (Edge → Fin 6) → ℝ := fun a => H (assignments z a).1 *
    ((if (assignments z a).2 m = c then (6 : ℝ) else 0) - 1)
  let S : (Fin 6 → Ω) → ℝ := fun x => ∑ a : Edge → Fin 6,
    ColeskiProductColorLaw.mass (weights W x) a * q a
  let F : (Fin 5 → Ω) → ℝ := fun b => ∑ a : BaseEdge → Fin 6,
    ColeskiProductColorLaw.mass (baseWeights W b) a * H a
  let T : (Fin 6 → Ω) → ℝ := fun x => F (fun j => x (z.succAbove j)) *
    (6 * W c (x (z.succAbove m),x z) - 1)
  have hST : S =ᵐ[Measure.pi (fun _ : Fin 6 => μ)] T := by
    filter_upwards [totals μ W ht,ae_star_weight μ W hs z m c] with x htotal hstar
    have hsum := ColeskiDeletedConditionalMoment.sum_incident z (weights W x) htotal H m c
    change S x = T x
    calc
      S x = (∑ b : BaseEdge → Fin 6,
        ColeskiProductColorLaw.mass (fun e => weights W x (base z e)) b * H b) *
          (6 * weights W x (ColeskiDeletedEdgeSplit.star z m) c - 1) := by
        simpa only [S,q,mul_assoc] using hsum
      _ = T x := by rw [hstar]; rfl
  have hS : Integrable S (Measure.pi (fun _ : Fin 6 => μ)) :=
    ColeskiWeightedIntegratedLaw.integrable_expectation _ _ (measurable_weights W hm) (bounds μ W hb) q
  have hT : Integrable T (Measure.pi (fun _ : Fin 6 => μ)) := hS.congr hST
  calc
    _ = ∫ x, S x ∂Measure.pi (fun _ : Fin 6 => μ) :=
      ColeskiWeightedIntegratedLaw.expectation _ _ (measurable_weights W hm) (bounds μ W hb) q
    _ = ∫ x, T x ∂Measure.pi (fun _ : Fin 6 => μ) := integral_congr_ae hST
    _ = 0 := ColeskiRootIntegralTransport.zero μ (W c) (hm c) (hb c) (hd c) z m F hT

end ColeskiGraphonConditionalBalance
#print axioms ColeskiGraphonConditionalBalance.balanced

/- END bundled local module GraphonConditionalBalance -/
