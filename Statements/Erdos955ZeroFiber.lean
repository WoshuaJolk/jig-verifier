import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Set.Nat

namespace Statements.Erdos955ZeroFiber

def s (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

/-- The zero fiber of the sum-of-proper-divisors map consists exactly
of the two boundary naturals 0 and 1. -/
abbrev statement : Prop :=
  {n : ℕ | s n = 0} = Set.Iic 1

theorem target : statement := sorry

end Statements.Erdos955ZeroFiber
