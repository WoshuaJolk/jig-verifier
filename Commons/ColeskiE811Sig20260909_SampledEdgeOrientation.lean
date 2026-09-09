import Commons.ColeskiE811Sig20260909_SixEdgePattern

/- BEGIN bundled local module SampledEdgeOrientation -/


namespace ColeskiSampledEdgeOrientation
open MeasureTheory ColeskiSixVertexLaw ColeskiSixEdgePattern
variable {Ω : Type*} [MeasurableSpace Ω]

theorem sampled_symmetry (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 6 → Ω × Ω → ℝ)
    (h : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1)) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin 6 => μ), ∀ e : Edge, ∀ c,
      W c (x e.val.1,x e.val.2) = W c (x e.val.2,x e.val.1) := by
  rw [ae_all_iff]
  intro e
  rw [ae_all_iff]
  intro c
  exact ColeskiSampledCoordinates.pair_ae_pullback μ (endpoints e) _ (h c)

theorem zero_directed_factor (W : Fin 6 → Ω × Ω → ℝ) (x : Fin 6 → Ω)
    (a : Edge → Fin 6)
    (hs : ∀ e : Edge, ∀ c, W c (x e.val.1,x e.val.2) = W c (x e.val.2,x e.val.1))
    (u v : Fin 6) (huv : u ≠ v)
    (hz : W (color a u v) (x u,x v) = 0) :
    ∃ e : Edge, weights W x e (a e) = 0 := by
  by_cases h : u < v
  · refine ⟨⟨(u,v),h⟩,?_⟩
    simpa [weights,color,h] using hz
  · have h' : v < u := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm huv)
    refine ⟨⟨(v,u),h'⟩,?_⟩
    have he := hs ⟨(v,u),h'⟩ (a ⟨(v,u),h'⟩)
    change W (a ⟨(v,u),h'⟩) (x v,x u) = 0
    rw [he]
    simpa [color,h,h'] using hz

end ColeskiSampledEdgeOrientation
#print axioms ColeskiSampledEdgeOrientation.sampled_symmetry
#print axioms ColeskiSampledEdgeOrientation.zero_directed_factor

/- END bundled local module SampledEdgeOrientation -/
