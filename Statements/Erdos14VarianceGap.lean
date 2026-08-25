import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos14VarianceGap

open scoped BigOperators

/-- A nonconstant integer profile has Cauchy defect linear in its support size. -/
abbrev statement : Prop :=
  ∀ {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ),
    (∃ a ∈ s, ∃ b ∈ s, f a ≠ f b) →
    s.card ≤
      2 * (s.card * (∑ i ∈ s, f i ^ 2) - (∑ i ∈ s, f i) ^ 2)

theorem target : statement := sorry

end Statements.Erdos14VarianceGap
