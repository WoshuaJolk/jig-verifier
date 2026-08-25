import Mathlib.NumberTheory.FactorisationProperties

namespace Statements.Erdos470OddWeird

/-- Erdős Problem 470(i): an odd weird number exists. -/
abbrev statement : Prop :=
  ∃ n : ℕ, n.Weird ∧ Odd n

theorem target : statement := sorry

end Statements.Erdos470OddWeird
