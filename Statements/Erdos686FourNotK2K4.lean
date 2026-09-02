import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdos686FourNotK2K4 — `N = 4` is not a ratio of two consecutive products of length 2 or 4

Erdős 686 (Jig 92) asks whether every `N ≥ 2` is `∏_{i=1}^k (m+i) / ∏_{i=1}^k (n+i)` for some
`k ≥ 2` and `m ≥ n + k`.  The non-square case is settled (`Erdos686NonSquareCase`), so what
remains is the perfect squares, and `N = 4` is the first square with no known representation.

This statement records the two easy lengths for `N = 4`, with no disjointness hypothesis at all:
for `k = 2` and `k = 4` the equation `4 ∏(n+i) = ∏(m+i)` has no solutions whatsoever.
Mechanism: `4(n+1)(n+2) = (2n+3)² − 1` and `(m+1)(m+2)(m+3)(m+4) = (m²+5m+5)² − 1`, so both
lengths reduce to `X² + 3 = Y²` with `X ≥ 3`, which has no solution since `Y > X` forces
`Y² ≥ X² + 2X + 1 > X² + 3`.  Prior art: both cases were observed in the erdosproblems.com
forum thread for 686 (Tao, `k = 2`; natso26, `k = 4`); this is the kernel-checked version.

Submissions **must not** import this module.
-/

namespace Statements.Erdos686FourNotK2K4

open scoped BigOperators

/-- For `k = 2` and `k = 4`, no `n, m` satisfy `4 = ∏_{i ≤ k}(m+i) / ∏_{i ≤ k}(n+i)`. -/
abbrev statement : Prop :=
  ∀ n m : ℕ,
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 2, (m + i)) / (∏ i ∈ Finset.Icc 1 2, (n + i)) ∧
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 4, (m + i)) / (∏ i ∈ Finset.Icc 1 4, (n + i))

theorem target : statement := sorry

end Statements.Erdos686FourNotK2K4
