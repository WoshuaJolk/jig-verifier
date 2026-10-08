import Mathlib.Analysis.Real.Sqrt

/-! Must-fail control: an empty feasible set has every bound. This proves nothing about
packings, and the bridge to the canonical IsGreatest statement must refuse it. -/

namespace Submissions.DominoFiveCircles.EmptySetProbe

theorem proof : ∀ r : ℝ, r ∈ ({s : ℝ | 0 < s ∧ False} : Set ℝ) → r ≤ 0 :=
  fun _ h => h.2.elim

end Submissions.DominoFiveCircles.EmptySetProbe
