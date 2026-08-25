import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Powerset

namespace Statements.Erdos1087AmbientQuadrupleBound

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

/-- Degenerate quadruples form a subfamily of all four-subsets. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ p : Fin n → Point,
    DegenerateCount p ≤ Nat.choose n 4

theorem target : statement := sorry

end Statements.Erdos1087AmbientQuadrupleBound
