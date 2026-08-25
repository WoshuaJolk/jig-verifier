import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod

open scoped Pointwise

namespace Statements.Erdos52SidonLowerBound

/-- A Sidon-set quadratic lower bound for the integer sum-product maximum. -/
abbrev statement : Prop :=
  ∀ A : Finset ℤ,
    (∀ a ∈ A, ∀ b ∈ A, a ≤ b →
      ∀ c ∈ A, ∀ d ∈ A, c ≤ d →
        a + b = c + d → a = c ∧ b = d) →
    (A + A).card = A.card + A.card.choose 2

theorem target : statement := sorry

end Statements.Erdos52SidonLowerBound
