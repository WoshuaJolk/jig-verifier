import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos10PrimeTwoPowers

/-- Natural numbers representable as a prime plus at most `k` powers of two, where repetitions of powers are allowed. -/
abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  {n | ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum}

/-- Erdős Problem 10: a uniform finite number of powers of two suffices for every sufficiently large natural number. -/
abbrev statement : Prop :=
  ∃ (k N : ℕ), ∀ n ≥ N, n ∈ sumPrimeAndTwoPows k

theorem target : statement := sorry

end Statements.Erdos10PrimeTwoPowers
