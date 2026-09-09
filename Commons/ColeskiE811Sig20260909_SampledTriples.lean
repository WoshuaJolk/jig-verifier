import Commons.ColeskiE811Sig20260909_SampledCoordinates

/- BEGIN bundled local module SampledTriples -/


namespace ColeskiSampledTriples
open MeasureTheory ColeskiSampledCoordinates
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem triple_preserving (i : Fin 3 ↪ I) :
    MeasurePreserving (fun x : I → Ω => (x (i 0), x (i 1), x (i 2)))
      (Measure.pi (fun _ : I => μ)) (μ.prod (μ.prod μ)) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0
  have h2 := (MeasurePreserving.id μ).prod
    (measurePreserving_piFinTwo (fun _ : Fin 2 => μ))
  convert h2.comp (h1.comp (preserving μ i)) using 1
  rfl

theorem ae_pullback (i : Fin 3 ↪ I) (P : Ω × Ω × Ω → Prop)
    (h : ∀ᵐ y ∂μ.prod (μ.prod μ), P y) :
    ∀ᵐ x ∂Measure.pi (fun _ : I => μ), P (x (i 0), x (i 1), x (i 2)) := by
  have hp := triple_preserving μ i
  apply ae_of_ae_map hp.measurable.aemeasurable
  rwa [hp.map_eq]

end ColeskiSampledTriples
#print axioms ColeskiSampledTriples.triple_preserving
#print axioms ColeskiSampledTriples.ae_pullback

/- END bundled local module SampledTriples -/
