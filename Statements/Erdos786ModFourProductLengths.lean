import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos786ModFourProductLengths

/-- Products of distinct integers congruent to two modulo four determine the
number of factors. -/
abbrev statement : Prop :=
  ∀ a b : Finset ℕ,
    (∀ i ∈ a, i % 4 = 2) →
    (∀ i ∈ b, i % 4 = 2) →
    a.prod id = b.prod id →
    a.card = b.card

theorem target : statement := sorry

end Statements.Erdos786ModFourProductLengths
