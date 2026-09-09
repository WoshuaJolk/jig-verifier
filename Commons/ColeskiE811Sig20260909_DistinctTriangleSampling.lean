import Commons.ColeskiE811Sig20260909_SampledTriples
import Commons.ColeskiE811Sig20260909_ZeroTriangleDensity

/- BEGIN bundled local module DistinctTriangleSampling -/


namespace ColeskiDistinctTriangleSampling
open MeasureTheory

def vertices (u v w : Fin 6) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : Fin 3 ↪ Fin 6 where
  toFun := ![u,v,w]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

theorem zero_sampled {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → Ω → Ω → ℝ)
    (hi : Integrable (fun p : Ω × Ω × Ω => f p.1 p.2.1 p.2.2) (μ.prod (μ.prod μ)))
    (hn : ∀ᵐ p ∂μ.prod (μ.prod μ), 0 ≤ f p.1 p.2.1 p.2.2)
    (hz : (∫ x, ∫ y, ∫ z, f x y z ∂μ ∂μ ∂μ) = 0)
    (u v w : Fin 6) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin 6 => μ), f (x u) (x v) (x w) = 0 := by
  exact ColeskiSampledTriples.ae_pullback μ (vertices u v w huv huw hvw) _
    (ColeskiZeroTriangleDensity.ae_zero_of_nested_integral μ f hi hn hz)

end ColeskiDistinctTriangleSampling
#print axioms ColeskiDistinctTriangleSampling.zero_sampled

/- END bundled local module DistinctTriangleSampling -/
