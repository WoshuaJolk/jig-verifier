import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod

open scoped Pointwise BigOperators

namespace Statements.Erdos52AdjacentRays

abbrev statement : Prop :=
  ∀ (A : Finset ℚ) (I : Finset ℕ) (l u : ℕ → ℚ) (B C : ℕ → Finset ℚ),
    (∀ i ∈ I, l i < u i) →
    (∀ i ∈ I, ∀ j ∈ I, i < j → u i ≤ l j) →
    (∀ i ∈ I, ∀ x ∈ B i, 0 < x ∧ x ∈ A ∧ l i * x ∈ A) →
    (∀ i ∈ I, ∀ y ∈ C i, 0 < y ∧ y ∈ A ∧ u i * y ∈ A) →
    (∑ i ∈ I, (B i).card * (C i).card) ≤ (A + A).card ^ 2

theorem target : statement := sorry

end Statements.Erdos52AdjacentRays
