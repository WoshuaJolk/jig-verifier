import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677LengthThreeCase

/-- Least common multiple of `{n+1, ..., n+k}`, as in Erdős problem 677. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- Erdős problem 677 for blocks of length three: disjoint blocks of three
consecutive integers never have the same least common multiple. -/
abbrev statement : Prop :=
  ∀ m n : ℕ, n + 3 ≤ m → lcmInterval m 3 ≠ lcmInterval n 3

theorem target : statement := sorry

end Statements.Erdos677LengthThreeCase
