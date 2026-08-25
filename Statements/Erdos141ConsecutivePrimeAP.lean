import Mathlib.NumberTheory.PrimeCounting

namespace Statements.Erdos141ConsecutivePrimeAP

def HasConsecutivePrimeAP (k : ℕ) : Prop :=
  ∃ (start step : ℕ), 0 < step ∧
    ∀ i < k,
      (start + i).nth Nat.Prime = start.nth Nat.Prime + i * step

/-- Erdős Problem 141: consecutive primes contain arithmetic
progressions of every finite length at least three. -/
abbrev statement : Prop :=
  ∀ k ≥ 3, HasConsecutivePrimeAP k

theorem target : statement := sorry

end Statements.Erdos141ConsecutivePrimeAP
