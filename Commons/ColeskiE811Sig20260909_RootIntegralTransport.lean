import Commons.ColeskiE811Sig20260909_DeletedVertexCoordinates
import Commons.ColeskiE811Sig20260909_RootDegreeMoment

/- BEGIN bundled local module RootIntegralTransport -/


namespace ColeskiRootIntegralTransport
open MeasureTheory ColeskiDeletedVertexCoordinates
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem zero (W : Ω × Ω → ℝ) (hm : Measurable W)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ W p ∧ W p ≤ 1)
    (hd : ∀ᵐ x ∂μ, (∫ y, W (x,y) ∂μ) = (1/6 : ℝ))
    (z : Fin 6) (m : Fin 5) (F : (Fin 5 → Ω) → ℝ)
    (hi : Integrable (fun x : Fin 6 → Ω => F (fun j => x (z.succAbove j)) *
      (6 * W (x (z.succAbove m),x z) - 1)) (Measure.pi (fun _ : Fin 6 => μ))) :
    (∫ x, F (fun j => x (z.succAbove j)) * (6 * W (x (z.succAbove m),x z) - 1)
      ∂Measure.pi (fun _ : Fin 6 => μ)) = 0 := by
  let G : (Fin 5 → Ω) × Ω → ℝ := fun p => F p.1 * (6 * W (p.1 m,p.2) - 1)
  have hp := preserving Ω μ z
  have hG : Integrable G ((Measure.pi (fun _ : Fin 5 => μ)).prod μ) :=
    (hp.integrable_comp_emb (split Ω z).measurableEmbedding).mp hi
  change (∫ x, G (split Ω z x) ∂Measure.pi (fun _ : Fin 6 => μ)) = 0
  rw [hp.integral_comp' G,integral_prod G hG]
  exact ColeskiRootDegreeMoment.deleted_vertex_integral μ W hm hb hd m F

end ColeskiRootIntegralTransport
#print axioms ColeskiRootIntegralTransport.zero

/- END bundled local module RootIntegralTransport -/
