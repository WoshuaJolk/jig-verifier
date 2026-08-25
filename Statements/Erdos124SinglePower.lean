import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

namespace Statements.Erdos124SinglePower

def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/-- A single admissible power belongs to the distinct-power sumset. -/
abbrev statement : Prop :=
  ∀ d k : ℕ, d ^ k ∈ sumsOfDistinctPowers d k

theorem target : statement := sorry

end Statements.Erdos124SinglePower
