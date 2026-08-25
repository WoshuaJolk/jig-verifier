import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos1049ParameterSpaceInhabited.Direct

theorem proof : ∃ t : ℚ, t > 1 := by
  exact ⟨3 / 2, by norm_num⟩

end Submissions.Erdos1049ParameterSpaceInhabited.Direct
