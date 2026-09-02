import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdos686FourNotK3 — `N = 4` is not a ratio of two disjoint consecutive products of length 3

With `v = m + 2`, `u = n + 2` the length-3 case of `4 ∏(n+i) = ∏(m+i)` is the cubic
`v³ − v = 4(u³ − u)`. Its integer points are exactly the nine trivial ones in `{−1,0,1}²` and
`±(2, 3)`; the point `(u, v) = (2, 3)` is `(n, m) = (0, 1)`, i.e. `2·3·4 / (1·2·3) = 4`, which
violates the disjointness `m ≥ n + 3`. So there is no admissible representation.

The integer points were determined by a descent to Thue equations (recorded in the statement's
message): the curve is birational to `W² = s³ − 48s + 272` via `s = 4(4v−u)/(v−4u)`,
`W = 60/(v−4u)`, integrality of the inverse map forces the denominator `b` of `W = b/d³` to
divide `60`, and the twelve Thue equations `a³ − 48ay² + 272y³ = b²`, `b ∣ 60`, were solved
with PARI/GP (`thue`, number-field data certified without GRH). Mathlib cannot express that
computation, so the statement is filed open.

Submissions **must not** import this module.
-/

namespace Statements.Erdos686FourNotK3

open scoped BigOperators

/-- No `n, m` with `m ≥ n + 3` satisfy `4 = ∏_{i ≤ 3}(m+i) / ∏_{i ≤ 3}(n+i)`. -/
abbrev statement : Prop :=
  ∀ n m : ℕ, n + 3 ≤ m →
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 3, (m + i)) / (∏ i ∈ Finset.Icc 1 3, (n + i))

theorem target : statement := sorry

end Statements.Erdos686FourNotK3
