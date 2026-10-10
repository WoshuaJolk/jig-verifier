import Mathlib.Analysis.Real.Sqrt

/-!
# DominoSevenCircles: seven equal circles in a 1 × 1/2 rectangle

Source: Packomania (Eckard Specht), "7 circles in a rectangle", aspect ratio 0.5,
https://www.packomania.com/crc_500/crc7_0.500000000000.html . The best known packing has no
symmetry: two zigzag rows with one circle centred at x = 1/2 + r, height r + 2r·sin 15°,
touching four others. Its radius is r = 1/(4 + √6 + √2) = 1/(4(1 + cos 15°))
= 0.12716654751512490887... . This statement asserts that value is optimal.

Encoding (identical to `Statements.DominoThreeCircles`). The rectangle is `[0,1] × [0,1/2]`.
A closed disk of radius `r` centred at `(x, y)` lies in it iff `r ≤ x ≤ 1 - r` and
`r ≤ y ≤ 1/2 - r`. Two disks of radius `r > 0` have disjoint interiors iff their centres are
at Euclidean distance at least `2r`, written with squared coordinates (deliberately NOT `dist`
on `ℝ × ℝ`, which is the sup metric).
-/

namespace Statements.DominoSevenCircles

/-- Seven closed disks of common radius `r` fit in `[0,1] × [0,1/2]` with pairwise disjoint
interiors. -/
def Packs (r : ℝ) : Prop :=
  ∃ c : Fin 7 → ℝ × ℝ,
    (∀ i, r ≤ (c i).1 ∧ (c i).1 ≤ 1 - r ∧ r ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - r) ∧
    (∀ i j, i ≠ j → (2 * r) ^ 2 ≤ ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2)

/-- The canonical proposition: `1/(4 + √6 + √2)` is the largest radius `r > 0` for which seven
equal circles pack in the 1 × 1/2 rectangle. -/
abbrev statement : Prop := IsGreatest {r : ℝ | 0 < r ∧ Packs r} (1 / (4 + Real.sqrt 6 + Real.sqrt 2))

theorem target : statement := sorry

end Statements.DominoSevenCircles
