import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos68PrimeLastOccurrence

/-- Every occurrence of a prime in the sequence `n! - 1` lies below the prime.
Consequently, from any occurrence one can choose a final occurrence `K < p`,
after which that prime divides no denominator at all. -/
abbrev statement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ, 2 ≤ n →
    p ∣ n.factorial - 1 →
    ∃ K : ℕ,
      n ≤ K ∧ K < p ∧ p ∣ K.factorial - 1 ∧
        ∀ m : ℕ, K < m → ¬p ∣ m.factorial - 1

theorem target : statement := sorry

end Statements.Erdos68PrimeLastOccurrence
