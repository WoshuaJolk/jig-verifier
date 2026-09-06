import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos830AmicablePairsInfinite

open ArithmeticFunction

/-- Erdős Problem 830, first question: `a, b` are an amicable pair when
`σ(a) = σ(b) = a + b`, and there are infinitely many such pairs. -/
abbrev statement : Prop :=
  {(a, b) : ℕ × ℕ | sigma 1 a = a + b ∧ sigma 1 b = a + b}.Infinite

theorem target : statement := sorry

end Statements.Erdos830AmicablePairsInfinite
