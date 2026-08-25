import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set MeasureTheory

namespace Submissions.Erdos120UnivAvoidance.OpenInterval

theorem proof :
    ∃ E : Set ℝ,
      MeasurableSet E ∧
      0 < volume E ∧
      ∀ a b : ℝ, a ≠ 0 →
        ¬ Set.image (fun x => a * x + b) (Set.univ : Set ℝ) ⊆ E := by
  refine ⟨Set.Ioo 0 1, measurableSet_Ioo, ?_, ?_⟩
  · norm_num
  · intro a b ha hsub
    have htwo : (2 : ℝ) ∈ Set.image (fun x => a * x + b) (Set.univ : Set ℝ) := by
      refine ⟨(2 - b) / a, Set.mem_univ _, ?_⟩
      field_simp
      ring
    have := hsub htwo
    norm_num at this

end Submissions.Erdos120UnivAvoidance.OpenInterval
