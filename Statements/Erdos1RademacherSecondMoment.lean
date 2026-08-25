import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace Statements.Erdos1RademacherSecondMoment

/-- The exact second moment of the centered subset sums (equivalently, of all
Rademacher signed sums) of a finite set of integers. -/
abbrev statement : Prop :=
  ∀ A : Finset ℤ,
    ∑ S ∈ A.powerset, (2 * (∑ x ∈ S, x) - ∑ x ∈ A, x) ^ 2 =
      2 ^ A.card * ∑ x ∈ A, x ^ 2

theorem target : statement := sorry

end Statements.Erdos1RademacherSecondMoment
