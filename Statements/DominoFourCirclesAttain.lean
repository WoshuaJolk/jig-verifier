import Mathlib.Analysis.Real.Sqrt

/-!
# DominoFourCirclesAttain: the Packomania zigzag is feasible

Attainment half of `Statements.DominoFourCircles`: four closed disks of radius
`(11 - 6√3)/4` fit in `[0,1] × [0,1/2]` with pairwise disjoint interiors (same encoding as the
root).
-/

namespace Statements.DominoFourCirclesAttain

abbrev statement : Prop :=
  ∃ c : Fin 4 → ℝ × ℝ,
    (∀ i, (11 - 6 * Real.sqrt 3) / 4 ≤ (c i).1 ∧ (c i).1 ≤ 1 - (11 - 6 * Real.sqrt 3) / 4 ∧
      (11 - 6 * Real.sqrt 3) / 4 ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - (11 - 6 * Real.sqrt 3) / 4) ∧
    (∀ i j, i ≠ j → (2 * ((11 - 6 * Real.sqrt 3) / 4)) ^ 2 ≤
      ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2)

theorem target : statement := sorry

end Statements.DominoFourCirclesAttain
