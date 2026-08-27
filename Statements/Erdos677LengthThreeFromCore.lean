import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677LengthThreeFromCore

/-- Least common multiple of `{n+1, ..., n+k}`, as in Erdős problem 677. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- The length-three case of Erdős problem 677 follows from the cubic core:
if `v³ - v = 2(u³ - u)` has no solution with `v ≥ u + 3`, then disjoint blocks of
three consecutive integers have different least common multiples. -/
abbrev statement : Prop :=
  (∀ u v : ℕ, u + 3 ≤ v → v ^ 3 + 2 * u ≠ 2 * u ^ 3 + v) →
    ∀ m n : ℕ, n + 3 ≤ m → lcmInterval m 3 ≠ lcmInterval n 3

theorem target : statement := sorry

end Statements.Erdos677LengthThreeFromCore
