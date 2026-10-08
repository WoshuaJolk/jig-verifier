import Mathlib.Analysis.Real.Sqrt

/-!
# DominoThreeCirclesAttain: the Packomania packing is feasible

Attainment half of `Statements.DominoThreeCircles`: three closed disks of radius
`(3 - √7)/2` fit in `[0,1] × [0,1/2]` with pairwise disjoint interiors (same encoding as the
root: box condition on centres, squared Euclidean centre distance at least `(2r)^2`).
-/

namespace Statements.DominoThreeCirclesAttain

abbrev statement : Prop :=
  ∃ c : Fin 3 → ℝ × ℝ,
    (∀ i, (3 - Real.sqrt 7) / 2 ≤ (c i).1 ∧ (c i).1 ≤ 1 - (3 - Real.sqrt 7) / 2 ∧
      (3 - Real.sqrt 7) / 2 ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - (3 - Real.sqrt 7) / 2) ∧
    (∀ i j, i ≠ j → (2 * ((3 - Real.sqrt 7) / 2)) ^ 2 ≤
      ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2)

theorem target : statement := sorry

end Statements.DominoThreeCirclesAttain
