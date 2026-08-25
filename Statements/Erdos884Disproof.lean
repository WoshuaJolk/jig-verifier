import Mathlib

namespace Statements.Erdos884Disproof

/-- The sum of reciprocal gaps over all ordered pairs of divisors. -/
noncomputable abbrev sumDivisorInvPairwiseDifference (n : ℕ) : ℝ :=
  ∑ j : Fin n.divisors.card, ∑ i : Fin j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i)

/-- The sum of reciprocal gaps between consecutive divisors. -/
noncomputable abbrev sumDivisorInvConsecutiveDifference (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

/-- Erdős Problem 884 has a negative answer: the pairwise divisor-gap sum is
not asymptotically bounded by the consecutive divisor-gap sum. -/
abbrev statement : Prop :=
  ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop]
    (1 + sumDivisorInvConsecutiveDifference))

theorem target : statement := sorry

end Statements.Erdos884Disproof
