import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

/-!
# Singleton case of Erdős problem 708

Every interval of `a` consecutive positive integers contains a multiple of
`a`, so a singleton input set has a cover of cardinality one.
-/

namespace Statements.Erdos708SingletonCover

abbrev statement : Prop :=
  ∀ a : ℕ, 2 ≤ a →
    ∀ s : ℕ, 1 ≤ s →
      ∃ B : Finset ℕ,
        B ⊆ Finset.Ico s (s + a) ∧
          B.card ≤ 1 ∧
            a ∣ ∏ b ∈ B, b

theorem target : statement := sorry

end Statements.Erdos708SingletonCover
