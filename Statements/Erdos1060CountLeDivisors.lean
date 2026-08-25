import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Finset
open scoped ArithmeticFunction.sigma

namespace Statements.Erdos1060CountLeDivisors

def solutionCount (n : ℕ) : ℕ :=
  #{k ≤ n | k * σ 1 k = n}

/-- Every solution `k` divides `n`, so the fiber embeds in the divisor set. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 < n → solutionCount n ≤ n.divisors.card

theorem target : statement := sorry

end Statements.Erdos1060CountLeDivisors
