import Mathlib.Data.Nat.Squarefree

namespace Statements.Erdos11SquarefreePowerTwo

/-- Erdős Problem 11: every odd natural number greater than one is a
squarefree natural number plus a power of two. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Odd n → 1 < n →
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

theorem target : statement := sorry

end Statements.Erdos11SquarefreePowerTwo
