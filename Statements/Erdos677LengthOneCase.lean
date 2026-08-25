import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677LengthOneCase

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- The conjecture holds for intervals of length one. -/
abbrev statement : Prop :=
  ∀ (m n : ℕ), m ≥ n + 1 → lcmInterval m 1 ≠ lcmInterval n 1

theorem target : statement := sorry

end Statements.Erdos677LengthOneCase
