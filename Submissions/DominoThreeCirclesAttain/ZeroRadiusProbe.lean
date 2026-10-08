import Mathlib.Analysis.Real.Sqrt

/-! Must-fail control: the degenerate radius-0 packing (all centres equal), which satisfies
the encoding with r = 0 but not with r = (3 - √7)/2. The bridge to the canonical type must
refuse it. -/

namespace Submissions.DominoThreeCirclesAttain.ZeroRadiusProbe

theorem proof : ∃ c : Fin 3 → ℝ × ℝ,
    (∀ i, (0 : ℝ) ≤ (c i).1 ∧ (c i).1 ≤ 1 - 0 ∧ (0 : ℝ) ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - 0) ∧
    (∀ i j, i ≠ j → (2 * (0 : ℝ)) ^ 2 ≤ ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2) :=
  ⟨fun _ => (0, 0), fun _ => ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩,
    fun _ _ _ => by simp⟩

end Submissions.DominoThreeCirclesAttain.ZeroRadiusProbe
