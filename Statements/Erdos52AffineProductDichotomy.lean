import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.RingTheory.Coprime.Basic

open scoped Pointwise

namespace Statements.Erdos52AffineProductDichotomy

abbrev statement : Prop :=
  ∀ (A : Finset ℤ) (u v L : ℤ),
    0 < v → 0 ≤ L → IsCoprime u v →
    (∀ a ∈ A, ∃ i : ℤ, 0 ≤ i ∧ i ≤ L ∧ a = u + v * i) →
    (∀ a ∈ A, |a| ≤ L ^ 2) ∨ A.card ^ 2 ≤ 2 * (A * A).card

theorem target : statement := sorry

end Statements.Erdos52AffineProductDichotomy
