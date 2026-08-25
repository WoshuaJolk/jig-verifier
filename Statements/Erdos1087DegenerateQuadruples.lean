import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos1087DegenerateQuadruples

open Filter
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

/-- The explicit `f(n) ≤ n^(3+o(1))` conjecture in Erdős Problem 1087. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      ∀ p : Fin n → Point, Function.Injective p →
        (DegenerateCount p : ℝ) ≤ Real.rpow n (3 + ε)

theorem target : statement := sorry

end Statements.Erdos1087DegenerateQuadruples
