import Mathlib.Data.Nat.Squarefree

namespace Submissions.Erdos969SquarefreeCountCeiling.Control

def squarefreeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Squarefree).card

theorem proof : False → ∀ n : ℕ, squarefreeCount n ≤ n + 1 := by
  intro h
  exact h.elim

end Submissions.Erdos969SquarefreeCountCeiling.Control
