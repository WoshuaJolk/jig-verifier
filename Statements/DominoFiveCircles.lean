import Mathlib.Analysis.Real.Sqrt

/-!
# DominoFiveCircles: five equal circles in a 1 × 1/2 rectangle

Source: Packomania (Eckard Specht), "5 circles in a rectangle", aspect ratio 0.5,
https://www.packomania.com/crc_500/crc5_0.500000000000.html . The best known packing is a
zigzag, three circles along the bottom edge and two along the top, with radius r = 9/2 - √19 = 0.141101056459326... .
This statement asserts that value is optimal.

Encoding (identical to `Statements.DominoThreeCircles`). The rectangle is `[0,1] × [0,1/2]`.
A closed disk of radius `r` centred at `(x, y)` lies in it iff `r ≤ x ≤ 1 - r` and
`r ≤ y ≤ 1/2 - r`. Two disks of radius `r > 0` have disjoint interiors iff their centres are
at Euclidean distance at least `2r`, written with squared coordinates (deliberately NOT `dist`
on `ℝ × ℝ`, which is the sup metric).
-/

namespace Statements.DominoFiveCircles

/-- 5 closed disks of common radius `r` fit in `[0,1] × [0,1/2]` with pairwise disjoint
interiors. -/
def Packs (r : ℝ) : Prop :=
  ∃ c : Fin 5 → ℝ × ℝ,
    (∀ i, r ≤ (c i).1 ∧ (c i).1 ≤ 1 - r ∧ r ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - r) ∧
    (∀ i j, i ≠ j → (2 * r) ^ 2 ≤ ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2)

/-- The canonical proposition: `9/2 - √19` is the largest radius `r > 0` for which 5
equal circles pack in the 1 × 1/2 rectangle. -/
abbrev statement : Prop := IsGreatest {r : ℝ | 0 < r ∧ Packs r} (9 / 2 - Real.sqrt 19)

theorem target : statement := sorry

end Statements.DominoFiveCircles
