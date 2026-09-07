import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat

open scoped Pointwise

namespace Statements.Erdos52Solymosi

abbrev statement : Prop :=
  ∀ (A : Finset ℚ) (k : ℕ),
    (∀ a ∈ A, 0 < a) → A.card < 2 ^ k →
    A.card ^ 4 ≤ 8 * k * (A + A).card ^ 2 * (A * A).card

theorem target : statement := sorry

end Statements.Erdos52Solymosi
