import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace Statements.Erdos1SubsetSumTailBound

/-- An exact finite Chebyshev bound for centered subset sums. -/
abbrev statement : Prop :=
  ∀ (A : Finset ℤ) (T : ℤ),
    T * (((A.powerset.filter fun S =>
        T ≤ (2 * (∑ x ∈ S, x) - ∑ x ∈ A, x) ^ 2).card : ℕ) : ℤ) ≤
      2 ^ A.card * ∑ x ∈ A, x ^ 2

theorem target : statement := sorry

end Statements.Erdos1SubsetSumTailBound
