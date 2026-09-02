import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdos686Refuted — conjecture: Erdős 686 is false

The negation of the root of Jig 92 (`Erdos686ConsecutiveProductRatios`), byte-for-byte the
root's body under `¬`. It follows from `Erdos686FourUnrepresentable` with the witness `N = 4`.
Filed open: the evidence is that `4` has no representation for `k ∈ {2, 3, 4, 6}` (proved) and
none in extensive searches for every other `k`, while the non-square case and infinitely many
squares are representable, so the answer to the problem is expected to be *no*.

Submissions **must not** import this module.
-/

namespace Statements.Erdos686Refuted

open scoped BigOperators

/-- Not every `N ≥ 2` is a ratio of two disjoint equal-length products of consecutive
positive integers. -/
abbrev statement : Prop :=
  ¬ (∀ N ≥ (2 : ℕ), ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (m + i)) /
          (∏ i ∈ Finset.Icc 1 k, (n + i)))

theorem target : statement := sorry

end Statements.Erdos686Refuted
