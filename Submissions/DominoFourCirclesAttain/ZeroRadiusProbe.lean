import Mathlib.Analysis.Real.Sqrt

/-! Must-fail control: the degenerate radius-0 packing (all centres equal). The bridge to the
canonical type must refuse it. -/

namespace Submissions.DominoFourCirclesAttain.ZeroRadiusProbe

theorem proof : ∃ c : Fin 4 → ℝ × ℝ,
    (∀ i, (0 : ℝ) ≤ (c i).1 ∧ (c i).1 ≤ 1 - 0 ∧ (0 : ℝ) ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - 0) ∧
    (∀ i j, i ≠ j → (2 * (0 : ℝ)) ^ 2 ≤ ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2) :=
  ⟨fun _ => (0, 0), fun _ => ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩,
    fun _ _ _ => by simp⟩

end Submissions.DominoFourCirclesAttain.ZeroRadiusProbe
