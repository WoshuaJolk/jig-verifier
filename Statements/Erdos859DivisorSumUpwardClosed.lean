import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos859DivisorSumUpwardClosed

def DivisorSumSet (t : ℕ) : Set ℕ :=
  {n : ℕ | ∃ s ⊆ Nat.divisors n, t = ∑ i ∈ s, i}

/-- Representability as a sum of distinct divisors is inherited by every
positive multiple. -/
abbrev statement : Prop :=
  ∀ t n m : ℕ, n ≠ 0 → m ≠ 0 → n ∣ m →
    n ∈ DivisorSumSet t → m ∈ DivisorSumSet t

theorem target : statement := sorry

end Statements.Erdos859DivisorSumUpwardClosed
