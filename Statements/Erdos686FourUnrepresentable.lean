import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdos686FourUnrepresentable — conjecture: `4` is not a ratio of disjoint consecutive products

The negative instance `N = 4` of Erdős 686. Equivalent (since `∏_{i ≤ k}(x+i) = k! · C(x+k, k)`)
to `C(m+k, k) ≠ 4 · C(n+k, k)` for all `k ≥ 2`, `m ≥ n + k`.

Known: `k = 2` and `k = 4` (`Erdos686FourNotK2K4`, kernel-checked), `k = 3`
(`Erdos686FourNotK3`, Thue descent), `k = 6` (Vjeko Kovač, erdosproblems.com forum, not
reproduced here). Open: `k = 5` and `k ≥ 7`. Evidence: no solution with `k = 5`, `n ≤ 10⁹`;
`k = 7..12`, `n ≤ 10⁸`; `k = 13..20`, `n ≤ 10⁷`; `k = 21..60`, `n ≤ 10⁶` (modular filter
mod `2⁶¹ − 1`, exact confirmation of hits — none). No congruence obstruction exists for any `k`
(for every modulus `M ≥ k` take `n = M − 1`, `m = 3M − k`), so a proof must be global.

Submissions **must not** import this module.
-/

namespace Statements.Erdos686FourUnrepresentable

open scoped BigOperators

/-- There are no `k ≥ 2`, `n`, `m ≥ n + k` with `4 = ∏_{i ≤ k}(m+i) / ∏_{i ≤ k}(n+i)`. -/
abbrev statement : Prop :=
  ¬ ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
      (4 : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i))

theorem target : statement := sorry

end Statements.Erdos686FourUnrepresentable
