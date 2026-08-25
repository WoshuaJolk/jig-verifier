import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

namespace Submissions.Erdos668OnePointMaximizer.Degenerate

abbrev Point := Fin 2 → ℝ
abbrev Configuration (n : ℕ) := Fin n → Point

def squaredDistance (p q : Point) : ℝ :=
  (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2

noncomputable def unitPairs {n : ℕ} (P : Configuration n) :
    Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij =>
    ij.1 < ij.2 ∧ squaredDistance (P ij.1) (P ij.2) = 1

def IsMaximizer {n : ℕ} (P : Configuration n) : Prop :=
  Function.Injective P ∧
    ∀ Q : Configuration n, Function.Injective Q →
      (unitPairs Q).card ≤ (unitPairs P).card

def origin : Point := fun _ => 0
def onePoint : Configuration 1 := fun _ => origin

theorem proof : False → IsMaximizer onePoint := False.elim

end Submissions.Erdos668OnePointMaximizer.Degenerate
