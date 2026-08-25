import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Powerset

namespace Submissions.Erdos1087AmbientQuadrupleBound.Direct

open scoped Classical

abbrev Point := EuclideanSpace ℝ (Fin 2)

def Degenerate {n : ℕ} (p : Fin n → Point) (Q : Finset (Fin n)) : Prop :=
  Q.card = 4 ∧
    ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q, ∃ d ∈ Q,
      a ≠ b ∧ c ≠ d ∧
      ({a, b} : Finset (Fin n)) ≠ {c, d} ∧
      dist (p a) (p b) = dist (p c) (p d)

noncomputable def DegenerateCount {n : ℕ} (p : Fin n → Point) : ℕ :=
  ((Finset.univ.powersetCard 4).filter fun Q => Degenerate p Q).card

theorem proof :
    ∀ n : ℕ, ∀ p : Fin n → Point,
      DegenerateCount p ≤ Nat.choose n 4 := by
  intro n p
  unfold DegenerateCount
  calc
    ((Finset.univ.powersetCard 4).filter fun Q => Degenerate p Q).card ≤
        (Finset.univ.powersetCard 4).card :=
      Finset.card_filter_le _ _
    _ = Nat.choose n 4 := by simp [Finset.card_powersetCard]

end Submissions.Erdos1087AmbientQuadrupleBound.Direct
