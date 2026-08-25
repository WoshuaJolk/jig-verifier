import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

/-!
# Erdős problem 708

Can the product of every finite set `A` of integers at least two be covered by
the product of at most `2|A|` members of every positive interval of
`max(A)` consecutive integers?
-/

namespace Statements.Erdos708ProductCover

abbrev statement : Prop :=
  ∀ (A : Finset ℕ) (hA : A.Nonempty),
    (∀ a ∈ A, 2 ≤ a) →
      ∀ s : ℕ, 1 ≤ s →
        ∃ B : Finset ℕ,
          B ⊆ Finset.Ico s (s + A.max' hA) ∧
            B.card ≤ 2 * A.card ∧
              (∏ a ∈ A, a) ∣ ∏ b ∈ B, b

theorem target : statement := sorry

end Statements.Erdos708ProductCover
