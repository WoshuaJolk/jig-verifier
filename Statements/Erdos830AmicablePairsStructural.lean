import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos830AmicablePairsStructural

open ArithmeticFunction

/-- Erdős Problem 830(i), with only public structural types in the canonical
interface: there are infinitely many pairs satisfying the source's two sigma
equalities. -/
abbrev statement : Prop :=
  {(a, b) : ℕ × ℕ |
    sigma 1 a = a + b ∧ sigma 1 b = a + b}.Infinite

theorem target : statement := sorry

end Statements.Erdos830AmicablePairsStructural
