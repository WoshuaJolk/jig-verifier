import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677LengthTwoCase

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- Disjoint intervals of length two have different least common multiples. -/
abbrev statement : Prop :=
  ∀ (m n : ℕ), m ≥ n + 2 →
    lcmInterval m 2 ≠ lcmInterval n 2

theorem target : statement := sorry

end Statements.Erdos677LengthTwoCase
