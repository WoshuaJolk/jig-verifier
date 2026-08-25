import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

namespace Statements.Erdos14UniqueSumLower

open Asymptotics Filter

/-- The natural numbers having exactly one representation, up to swapping,
as a sum of two elements of `A`. -/
def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

/-- The number of positive integers at most `N` without a unique
unordered representation as a sum of two elements of `A`. -/
noncomputable def exceptionCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ uniquePairSums A).ncard

/-- The comparison function `N ↦ N^(1/2-ε)`. -/
noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  Real.rpow N (1 / 2 - ε)

/-- Erdős Problem 14, first question: for every set `A` and every
positive `ε`, the exception count is `Ω(N^(1/2-ε))`. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, ∀ ε : ℝ, 0 < ε →
    Asymptotics.IsBigO atTop (almostSquareRoot ε) (exceptionCount A)

theorem target : statement := sorry

end Statements.Erdos14UniqueSumLower
