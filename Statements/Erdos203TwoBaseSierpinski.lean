import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos203TwoBaseSierpinski

/-- Erdős Problem 203: a number coprime to six whose entire two-parameter
`2^k * 3^l` orbit becomes composite after adding one. -/
abbrev statement : Prop :=
  ∃ m : ℕ, m.Coprime 6 ∧
    ∀ k l : ℕ, ¬(2 ^ k * 3 ^ l * m + 1).Prime

theorem target : statement := sorry

end Statements.Erdos203TwoBaseSierpinski
