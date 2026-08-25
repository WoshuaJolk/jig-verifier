import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Finset
open scoped ArithmeticFunction.sigma

namespace Statements.Erdos1060CountDomainBound

def solutionCount (n : ℕ) : ℕ :=
  #{k ≤ n | k * σ 1 k = n}

/-- The solution count cannot exceed the size of its defining interval. -/
abbrev statement : Prop :=
  ∀ n : ℕ, solutionCount n ≤ n + 1

theorem target : statement := sorry

end Statements.Erdos1060CountDomainBound
