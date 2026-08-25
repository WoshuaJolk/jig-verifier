import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Function
open ArithmeticFunction.sigma

namespace Statements.Erdos412SigmaOrbitsIntersect

/-- Erdős Problem 412: any two sum-of-divisors trajectories eventually intersect. -/
abbrev statement : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ n : ℕ, 2 ≤ n →
    ∃ i j : ℕ, ((σ 1)^[i]) m = ((σ 1)^[j]) n

theorem target : statement := sorry

end Statements.Erdos412SigmaOrbitsIntersect
