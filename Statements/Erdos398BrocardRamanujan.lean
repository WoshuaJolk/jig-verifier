import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos398BrocardRamanujan

/-- The Brocard--Ramanujan conjecture: the only natural `n` for which
`n! + 1` is a square are `4`, `5`, and `7`. -/
abbrev statement : Prop :=
  {n : ℕ | ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2} = {4, 5, 7}

theorem target : statement := sorry

end Statements.Erdos398BrocardRamanujan
