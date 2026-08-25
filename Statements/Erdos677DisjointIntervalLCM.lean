import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677DisjointIntervalLCM

/-- Least common multiple of `{n+1, ..., n+k}`. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- Erdős problem 677: disjoint intervals of the same positive length have different least common multiples. -/
abbrev statement : Prop :=
  ∀ (m n k : ℕ), k > 0 → m ≥ n + k →
    lcmInterval m k ≠ lcmInterval n k

theorem target : statement := sorry

end Statements.Erdos677DisjointIntervalLCM
