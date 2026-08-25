import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos686InfiniteSquareFamily

open scoped BigOperators

/-- The infinite square family `4(2t+3)²` is representable with block
length two. -/
abbrev statement : Prop :=
  ∀ t : ℕ, ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
    ((4 * (2 * t + 3) ^ 2 : ℕ) : ℚ) =
      (∏ i ∈ Finset.Icc 1 k, (m + i)) /
        (∏ i ∈ Finset.Icc 1 k, (n + i))

theorem target : statement := sorry

end Statements.Erdos686InfiniteSquareFamily
