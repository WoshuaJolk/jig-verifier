import Mathlib.Data.Finset.NatAntidiagonal

namespace Statements.Erdos28UnivZeroCount

/-- Zero has exactly one ordered representation as a sum of two natural numbers. -/
abbrev statement : Prop :=
  (Finset.antidiagonal 0).card = 1

theorem target : statement := sorry

end Statements.Erdos28UnivZeroCount
