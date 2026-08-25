import Mathlib

namespace Statements.Erdos384EcklundPrimeDivisor

/-- The unique exception in Ecklund's source range `2 * k ≤ n`. -/
abbrev IsException (n k : ℕ) : Prop :=
  n = 7 ∧ k = 3

/-- Erdős Problem 384 with the inclusive boundary stated by Ecklund.

The integral inequality `2 * p ≤ n` is exactly `p ≤ n / 2`, without
introducing truncated natural-number division. -/
abbrev statement : Prop :=
  ∀ n k : ℕ, 1 < k → 2 * k ≤ n → ¬ IsException n k →
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n k ∧ 2 * p ≤ n

theorem target : statement := sorry

end Statements.Erdos384EcklundPrimeDivisor
