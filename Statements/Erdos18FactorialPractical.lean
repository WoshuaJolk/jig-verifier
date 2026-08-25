import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18FactorialPractical

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

/-- Every factorial is practical: each natural target at most `n!` is a sum of
distinct divisors of `n!`. -/
abbrev statement : Prop :=
  ∀ n m : ℕ, m ≤ n.factorial → m ∈ subsetSums n.factorial.divisors

theorem target : statement := sorry

end Statements.Erdos18FactorialPractical
