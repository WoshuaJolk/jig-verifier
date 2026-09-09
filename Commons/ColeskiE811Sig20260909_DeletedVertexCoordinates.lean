import Mathlib

/- BEGIN bundled local module DeletedVertexCoordinates -/


namespace ColeskiDeletedVertexCoordinates
open MeasureTheory
variable (Ω : Type*) [MeasurableSpace Ω]

def split (z : Fin 6) : (Fin 6 → Ω) ≃ᵐ (Fin 5 → Ω) × Ω :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 6 => Ω) z).trans
    MeasurableEquiv.prodComm

theorem split_apply (z : Fin 6) (x : Fin 6 → Ω) :
    split Ω z x = ((fun m => x (z.succAbove m)),x z) := rfl

theorem root (z : Fin 6) (b : Fin 5 → Ω) (r : Ω) :
    (split Ω z).symm (b,r) z = r := by
  have h := congrArg Prod.snd ((split Ω z).apply_symm_apply (b,r))
  exact h

theorem retained (z : Fin 6) (b : Fin 5 → Ω) (r : Ω) (m : Fin 5) :
    (split Ω z).symm (b,r) (z.succAbove m) = b m := by
  have h := congrArg (fun p : (Fin 5 → Ω) × Ω => p.1 m)
    ((split Ω z).apply_symm_apply (b,r))
  exact h

theorem preserving (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Fin 6) :
    MeasurePreserving (split Ω z) (Measure.pi (fun _ : Fin 6 => μ))
      ((Measure.pi (fun _ : Fin 5 => μ)).prod μ) := by
  exact Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 6 => μ) z)

end ColeskiDeletedVertexCoordinates
#print axioms ColeskiDeletedVertexCoordinates.preserving
#print axioms ColeskiDeletedVertexCoordinates.retained

/- END bundled local module DeletedVertexCoordinates -/
