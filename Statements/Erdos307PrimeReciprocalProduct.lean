import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos307PrimeReciprocalProduct

/-- Erdős Problem 307 (asked by Barbeau, 1976). Are there two finite sets of primes `P`
and `Q` with `(∑_{p ∈ P} 1/p) · (∑_{q ∈ Q} 1/q) = 1`? -/
abbrev statement : Prop :=
  ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1

theorem target : statement := sorry

end Statements.Erdos307PrimeReciprocalProduct
