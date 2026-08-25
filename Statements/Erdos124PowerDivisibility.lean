import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Statements.Erdos124PowerDivisibility

def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/-- Every shifted distinct-power sum is divisible by the cutoff power. -/
abbrev statement : Prop :=
  ∀ d k n : ℕ, n ∈ sumsOfDistinctPowers d k → d ^ k ∣ n

theorem target : statement := sorry

end Statements.Erdos124PowerDivisibility
