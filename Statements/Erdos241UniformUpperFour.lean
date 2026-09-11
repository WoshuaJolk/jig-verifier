import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Statements.Erdos241UniformUpperFour
open Finset

/-- Explicit quantitative finite form of the classical cubic upper-four bound.
The repeated-summand B3 condition is the root condition. -/
abbrev statement : Prop :=
  ∀ m N : ℕ, 1 ≤ m → m * (48 * m * (m + 2)) ^ 3 ≤ N →
    ∀ A : Finset ℕ, A ⊆ Icc 1 N →
      (∀ m₁ m₂ : Multiset ℕ,
        m₁.card = 3 → m₂.card = 3 →
        (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
        m₁.sum = m₂.sum → m₁ = m₂) →
      m * A.card ^ 3 ≤ (4 * m + 9) * N

end Statements.Erdos241UniformUpperFour
