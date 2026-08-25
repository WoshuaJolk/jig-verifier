import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Function
open ArithmeticFunction.sigma

namespace Statements.Erdos412EqualStartsIntersect

/-- Equal starting values have intersecting sum-of-divisors trajectories. -/
abbrev statement : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    ∃ i j : ℕ, ((σ 1)^[i]) m = ((σ 1)^[j]) m

theorem target : statement := sorry

end Statements.Erdos412EqualStartsIntersect
