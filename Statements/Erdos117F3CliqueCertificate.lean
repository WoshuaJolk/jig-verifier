import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

namespace Statements.Erdos117F3CliqueCertificate

abbrev Vec := Fin 6 → ZMod 3

/-- The standard rank-six symplectic form used in Lemma 4.4. -/
def symplecticForm (x y : Vec) : ZMod 3 :=
  x 0 * y 1 - x 1 * y 0 +
  x 2 * y 3 - x 3 * y 2 +
  x 4 * y 5 - x 5 * y 4

/-- The thirteen projective representatives printed in Lemma 4.4. -/
def vectors : Fin 13 → Vec :=
  ![
    ![1, 2, 0, 2, 1, 1],
    ![0, 1, 1, 0, 0, 2],
    ![0, 1, 0, 1, 0, 0],
    ![0, 1, 1, 2, 2, 1],
    ![1, 2, 1, 0, 2, 0],
    ![1, 1, 0, 1, 2, 2],
    ![1, 0, 0, 1, 2, 0],
    ![1, 0, 1, 1, 2, 1],
    ![1, 1, 1, 0, 0, 1],
    ![1, 2, 0, 0, 2, 1],
    ![1, 0, 0, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1],
    ![1, 2, 0, 1, 1, 0]
  ]

/-- Every two distinct listed vectors have nonzero symplectic pairing. -/
abbrev statement : Prop :=
  ∀ i j : Fin 13, i ≠ j →
    symplecticForm (vectors i) (vectors j) ≠ 0

theorem target : statement := sorry

end Statements.Erdos117F3CliqueCertificate
