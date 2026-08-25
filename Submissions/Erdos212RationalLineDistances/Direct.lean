import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order

namespace Submissions.Erdos212RationalLineDistances.Direct

theorem proof :
    (Set.range fun q : ℚ => (q : ℂ)).Pairwise
      fun z₁ z₂ => dist z₁ z₂ ∈ Set.range Rat.cast := by
  intro x hx y hy hxy
  obtain ⟨qx, rfl⟩ := hx
  obtain ⟨qy, rfl⟩ := hy
  refine ⟨|qx - qy|, ?_⟩
  simpa [Complex.dist_eq] using (Complex.norm_ratCast (qx - qy)).symm

end Submissions.Erdos212RationalLineDistances.Direct
