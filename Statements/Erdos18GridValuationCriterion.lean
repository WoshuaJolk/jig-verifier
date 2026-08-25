import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18GridValuationCriterion

/-- The complementary-divisor grid reduces quotient coverage to prime
valuation bounds for one cofactor. The isolated `n=29` grid failure is included
to show that the criterion is exact rather than vacuous. -/
abbrev statement : Prop :=
  (∀ k a b c u d v : ℕ,
    6 ≤ k →
    a < k - 2 →
    b < k - 1 →
    c < k →
    0 < u →
    0 < d →
    d < k →
    0 < v →
    u * d = k - c →
    u + v = a * (k - 1) + b + 1 →
    u ≠ k - d →
    k * v ≠ u * (k - d) →
    (∀ p : ℕ, p.Prime →
      v.factorization p ≤ (k - 1).factorial.factorization p) →
    ∃ E : Finset ℕ,
      E ⊆ k.factorial.divisors ∧
      E.card = 2 ∧
      a * k * (k - 1) + b * k + c = E.sum id) ∧
  (∀ u d v : ℕ, 0 < u → 0 < d →
    u * d = 9 →
    u + v = 650 →
    ¬(v ∣ Nat.factorial 27))

theorem target : statement := sorry

end Statements.Erdos18GridValuationCriterion
