import Commons.ColeskiE811Sig20260909_SampledEdgeOrientation

/- BEGIN bundled local module SampledTriangleSupport -/


namespace ColeskiSampledTriangleSupport
open MeasureTheory ColeskiSixVertexLaw ColeskiSixEdgePattern ColeskiSampledEdgeOrientation
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem zero_mass (W : Fin 6 → Ω × Ω → ℝ) (a : Edge → Fin 6)
    (hs : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (u v w : Fin 6) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hz : ∀ᵐ x ∂Measure.pi (fun _ : Fin 6 => μ),
      W (color a u v) (x u,x v) * W (color a v w) (x v,x w) *
        W (color a u w) (x w,x u) = 0) : mass μ W a = 0 := by
  apply ColeskiIntegratedColorLaw.zero_of_ae_zero_factor
  filter_upwards [sampled_symmetry μ W hs,hz] with x hx hz
  rcases (mul_eq_zero.mp hz) with h | h
  · rcases (mul_eq_zero.mp h) with h | h
    · exact zero_directed_factor W x a hx u v huv h
    · exact zero_directed_factor W x a hx v w hvw h
  · apply zero_directed_factor W x a hx w u (Ne.symm huw)
    rwa [symmetric a w u]

theorem supported (W : Fin 6 → Ω × Ω → ℝ)
    (hs : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hz : ∀ (a : Edge → Fin 6) (u v w : Fin 6), u ≠ v → u ≠ w → v ≠ w →
      ColeskiK4Coverage.good (color a u v) (color a u w) (color a v w) ≠ true →
      ∀ᵐ x ∂Measure.pi (fun _ : Fin 6 => μ),
        W (color a u v) (x u,x v) * W (color a v w) (x v,x w) *
          W (color a u w) (x w,x u) = 0)
    (a : Edge → Fin 6) (ha : 0 < mass μ W a) :
    ColeskiPatternValidity.Valid (pattern a) := by
  apply valid
  intro u v w huv huw hvw
  by_contra h
  have hm := zero_mass μ W a hs u v w huv huw hvw (hz a u v w huv huw hvw h)
  rw [hm] at ha
  exact (lt_irrefl 0) ha

end ColeskiSampledTriangleSupport
#print axioms ColeskiSampledTriangleSupport.zero_mass
#print axioms ColeskiSampledTriangleSupport.supported

/- END bundled local module SampledTriangleSupport -/
