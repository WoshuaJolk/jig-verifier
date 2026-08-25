import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos830InfinitelyManyAmicablePairs

open ArithmeticFunction

/-- Two natural numbers are amicable when each has divisor sum equal to
their sum. This follows the explicit convention in the cited source. -/
structure IsAmicable (a b : ℕ) : Prop where
  left : sigma 1 a = a + b
  right : sigma 1 b = a + b

/-- Erdős Problem 830(i): there are infinitely many amicable pairs. -/
abbrev statement : Prop :=
  {(a, b) : ℕ × ℕ | IsAmicable a b}.Infinite

theorem target : statement := sorry

end Statements.Erdos830InfinitelyManyAmicablePairs
