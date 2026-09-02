import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdos686SquaresNotK3 — the squares `25, 49, 81, 121, 144` have no length-3 representation

Same descent as `Erdos686FourNotK3`, for `N = c`: `v³ − v = c(u³ − u)` is birational to
`W² = s³ − 3c²s + c²(c²+1)` via `s = c(cv − u)/(v − cu)`, `W = (c³ − c)/(v − cu)`; integrality of
`u = (s − c²)/W`, `v = c(s − 1)/W` forces the denominator of `W` to divide `c³ − c`, and the
resulting Thue equations were solved with PARI/GP (certified). For each of these five squares the
only integer points of the cubic are the nine trivial ones in `{−1,0,1}²`. (Validation: the same
procedure returns exactly the known points `(u,v) = (13, 27)` for `N = 9` and `(6, 15)` for
`N = 16`.) `N = 64` is excluded because `64` is a cube and the form is reducible.

Submissions **must not** import this module.
-/

namespace Statements.Erdos686SquaresNotK3

open scoped BigOperators

/-- For `N ∈ {25, 49, 81, 121, 144}`, no `n, m` with `m ≥ n + 3` satisfy
`N = ∏_{i ≤ 3}(m+i) / ∏_{i ≤ 3}(n+i)`. -/
abbrev statement : Prop :=
  ∀ N ∈ ({25, 49, 81, 121, 144} : Finset ℕ), ∀ n m : ℕ, n + 3 ≤ m →
    (N : ℚ) ≠ (∏ i ∈ Finset.Icc 1 3, (m + i)) / (∏ i ∈ Finset.Icc 1 3, (n + i))

theorem target : statement := sorry

end Statements.Erdos686SquaresNotK3
