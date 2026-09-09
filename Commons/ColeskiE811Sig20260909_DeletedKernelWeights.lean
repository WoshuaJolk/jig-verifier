import Commons.ColeskiE811Sig20260909_DeletedVertexCoordinates
import Commons.ColeskiE811Sig20260909_DeletedAssignmentSplit
import Commons.ColeskiE811Sig20260909_SampledEdgeOrientation

/- BEGIN bundled local module DeletedKernelWeights -/


namespace ColeskiDeletedKernelWeights
open MeasureTheory ColeskiSixVertexLaw ColeskiDeletedEdgeSplit
open ColeskiDeletedVertexCoordinates
variable {Ω : Type*} [MeasurableSpace Ω]

def baseWeights (W : Fin 6 → Ω × Ω → ℝ) (b : Fin 5 → Ω) (e : BaseEdge) (c : Fin 6) : ℝ :=
  W c (b e.val.1,b e.val.2)

theorem base_weights (W : Fin 6 → Ω × Ω → ℝ) (z : Fin 6)
    (b : Fin 5 → Ω) (r : Ω) (e : BaseEdge) (c : Fin 6) :
    weights W ((split Ω z).symm (b,r)) (base z e) c = baseWeights W b e c := by
  simp [weights,base,baseWeights,retained]

theorem star_weight (W : Fin 6 → Ω × Ω → ℝ) (x : Fin 6 → Ω)
    (hs : ∀ e : Edge, ∀ c, W c (x e.val.1,x e.val.2) = W c (x e.val.2,x e.val.1))
    (z : Fin 6) (m : Fin 5) (c : Fin 6) :
    weights W x (ColeskiDeletedEdgeSplit.star z m) c = W c (x (z.succAbove m),x z) := by
  by_cases h : z < z.succAbove m
  · have he := hs (ColeskiDeletedEdgeSplit.star z m) c
    simpa [weights,ColeskiDeletedEdgeSplit.star,min_eq_left (le_of_lt h),max_eq_right (le_of_lt h)] using he
  · have hh : z.succAbove m < z := lt_of_le_of_ne (le_of_not_gt h) (Fin.succAbove_ne z m)
    simp [weights,ColeskiDeletedEdgeSplit.star,min_eq_right (le_of_lt hh),max_eq_left (le_of_lt hh)]

theorem ae_star_weight (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 6 → Ω × Ω → ℝ)
    (hs : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1)) (z : Fin 6) (m : Fin 5) (c : Fin 6) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin 6 => μ),
      weights W x (ColeskiDeletedEdgeSplit.star z m) c = W c (x (z.succAbove m),x z) := by
  filter_upwards [ColeskiSampledEdgeOrientation.sampled_symmetry μ W hs] with x hx
  exact star_weight W x hx z m c

end ColeskiDeletedKernelWeights
#print axioms ColeskiDeletedKernelWeights.base_weights
#print axioms ColeskiDeletedKernelWeights.ae_star_weight

/- END bundled local module DeletedKernelWeights -/
