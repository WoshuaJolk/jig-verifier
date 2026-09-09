import Mathlib

/- BEGIN bundled local module SampledCoordinates -/


namespace ColeskiSampledCoordinates
open MeasureTheory ProbabilityTheory
variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem preserving (i : J ↪ I) :
    MeasurePreserving (fun x : I → Ω => fun j => x (i j))
      (Measure.pi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) := by
  classical
  have hi : iIndepFun (fun k : I => fun x : I → Ω => x k)
      (Measure.pi (fun _ : I => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hj := hi.precomp i.injective
  refine ⟨by fun_prop, ?_⟩
  have hm := hj.map_fun_eq_pi_map (fun j => (measurable_pi_apply (i j)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : I => μ) _).map_eq] using hm

theorem ae_pullback (i : J ↪ I) (P : (J → Ω) → Prop)
    (h : ∀ᵐ y ∂Measure.pi (fun _ : J => μ), P y) :
    ∀ᵐ x ∂Measure.pi (fun _ : I => μ), P (fun j => x (i j)) := by
  have hp := preserving μ i
  apply ae_of_ae_map hp.measurable.aemeasurable
  rwa [hp.map_eq]

theorem pair_preserving (i : Fin 2 ↪ I) :
    MeasurePreserving (fun x : I → Ω => (x (i 0), x (i 1)))
      (Measure.pi (fun _ : I => μ)) (μ.prod μ) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinTwo_apply] using
    (measurePreserving_piFinTwo (fun _ : Fin 2 => μ)).comp (preserving μ i)

theorem pair_ae_pullback (i : Fin 2 ↪ I) (P : Ω × Ω → Prop)
    (h : ∀ᵐ y ∂μ.prod μ, P y) :
    ∀ᵐ x ∂Measure.pi (fun _ : I => μ), P (x (i 0), x (i 1)) := by
  have hp := pair_preserving μ i
  apply ae_of_ae_map hp.measurable.aemeasurable
  rwa [hp.map_eq]

end ColeskiSampledCoordinates
#print axioms ColeskiSampledCoordinates.preserving
#print axioms ColeskiSampledCoordinates.ae_pullback
#print axioms ColeskiSampledCoordinates.pair_ae_pullback

/- END bundled local module SampledCoordinates -/
