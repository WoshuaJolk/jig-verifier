import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

namespace Statements.Erdos14LargeEpsilon

open Asymptotics Filter

/-- Natural numbers having exactly one unordered representation as a
sum of two elements of `A`. -/
def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ uniquePairSums A).ncard

noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  Real.rpow N (1 / 2 - ε)

/-- The universal part of the Erdős lower bound where its comparison
function is bounded above by one. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, ∀ ε : ℝ, 1 / 2 ≤ ε →
    Asymptotics.IsBigO atTop (almostSquareRoot ε) (exceptionCount A)

theorem target : statement := sorry

end Statements.Erdos14LargeEpsilon
