import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos686NonSquareCase

open scoped BigOperators

/-- **Erdős problem 686 for every non-square `N`.**

Every integer `N ≥ 2` that is not a perfect square is a ratio of two disjoint
equal-length products of consecutive positive integers.  The full problem, over
all `N ≥ 2`, is the canonical statement of Jig 92; this is the non-square half,
and it is settled: `k = 2` always works, by the Pell equation `x² - N y² = 1`.

What remains of Erdős 686 is therefore exactly the perfect squares. -/
abbrev statement : Prop :=
  ∀ N ≥ (2 : ℕ), ¬ IsSquare N →
    ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (m + i)) /
          (∏ i ∈ Finset.Icc 1 k, (n + i))

theorem target : statement := sorry

end Statements.Erdos686NonSquareCase
