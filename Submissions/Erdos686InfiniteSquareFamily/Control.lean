import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos686InfiniteSquareFamily.Control

open scoped BigOperators

abbrev claimedStatement : Prop :=
  ∀ t : ℕ, ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
    ((4 * (2 * t + 3) ^ 2 : ℕ) : ℚ) =
      (∏ i ∈ Finset.Icc 1 k, (m + i)) /
        (∏ i ∈ Finset.Icc 1 k, (n + i))

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos686InfiniteSquareFamily.Control
