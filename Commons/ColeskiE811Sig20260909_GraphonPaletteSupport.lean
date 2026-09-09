import Commons.ColeskiE811Sig20260909_TriangleIntegrability
import Commons.ColeskiE811Sig20260909_DistinctTriangleSampling
import Commons.ColeskiE811Sig20260909_SampledTriangleSupport
import Commons.ColeskiE811Sig20260909_K4SemanticsOnly

/- BEGIN bundled local module GraphonPaletteSupport -/


namespace ColeskiGraphonPaletteSupport
open MeasureTheory ColeskiSixVertexLaw ColeskiSixEdgePattern ColeskiK4Coverage
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem supported (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hs : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hz : ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
      ({i,j,k} : Finset (Fin 6)) ∉ palettes →
      (∫ x, ∫ y, ∫ z, W i (x,y) * W j (y,z) * W k (z,x) ∂μ ∂μ ∂μ) = 0)
    (a : Edge → Fin 6) (ha : 0 < mass μ W a) :
    ColeskiPatternValidity.Valid (pattern a) := by
  apply ColeskiSampledTriangleSupport.supported μ W hs _ a ha
  intro b u v w huv huw hvw hbad
  let i := color b u v
  let j := color b v w
  let k := color b u w
  have hnot : ¬ (i = k ∨ k = j ∨ i = j ∨ ({i,k,j} : Finset (Fin 6)) ∈ palettes) := by
    intro h
    exact hbad ((good_iff i k j).mpr h)
  have hij : i ≠ j := fun h => hnot (Or.inr (Or.inr (Or.inl h)))
  have hjk : j ≠ k := fun h => hnot (Or.inr (Or.inl h.symm))
  have hik : i ≠ k := fun h => hnot (Or.inl h)
  have hpal : ({i,j,k} : Finset (Fin 6)) ∉ palettes := by
    intro h
    apply hnot
    right; right; right
    have he : ({i,k,j} : Finset (Fin 6)) = {i,j,k} := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    rwa [he]
  apply ColeskiDistinctTriangleSampling.zero_sampled μ _
    (ColeskiTriangleIntegrability.integrable μ _ _ _ (hm i) (hm j) (hm k) (hb i) (hb j) (hb k))
    _ (hz i j k hij hjk hik hpal) u v w huv huw hvw
  filter_upwards [ColeskiTriangleIntegrability.bounds μ _ _ _ (hb i) (hb j) (hb k)] with p hp
  exact hp.1

end ColeskiGraphonPaletteSupport
#print axioms ColeskiGraphonPaletteSupport.supported

/- END bundled local module GraphonPaletteSupport -/
