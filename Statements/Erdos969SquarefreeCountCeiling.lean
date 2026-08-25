import Mathlib.Data.Nat.Squarefree

namespace Statements.Erdos969SquarefreeCountCeiling

def squarefreeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Squarefree).card

/-- The squarefree count cannot exceed the size of its inclusive search range. -/
abbrev statement : Prop :=
  ∀ n : ℕ, squarefreeCount n ≤ n + 1

theorem target : statement := sorry

end Statements.Erdos969SquarefreeCountCeiling
