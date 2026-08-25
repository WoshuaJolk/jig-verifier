import Mathlib.NumberTheory.ArithmeticFunction.Misc

open ArithmeticFunction.sigma

namespace Statements.Erdos412TwoReachesThree

/-- The sum-of-divisors trajectory from two reaches three in one step. -/
abbrev statement : Prop :=
  (σ 1) 2 = 3

theorem target : statement := sorry

end Statements.Erdos412TwoReachesThree
