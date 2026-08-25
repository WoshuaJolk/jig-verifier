import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos686ConsecutiveProductRatios

open scoped BigOperators

/-- Erdős Problem 686: every integer at least two is a ratio of two
equal-length products of consecutive positive integers, with disjoint blocks. -/
abbrev statement : Prop :=
  ∀ N ≥ (2 : ℕ), ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
    (N : ℚ) =
      (∏ i ∈ Finset.Icc 1 k, (m + i)) /
        (∏ i ∈ Finset.Icc 1 k, (n + i))

theorem target : statement := sorry

end Statements.Erdos686ConsecutiveProductRatios
