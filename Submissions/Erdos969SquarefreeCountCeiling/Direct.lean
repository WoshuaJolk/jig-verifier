import Mathlib.Data.Nat.Squarefree

namespace Submissions.Erdos969SquarefreeCountCeiling.Direct

def squarefreeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Squarefree).card

theorem proof : ∀ n : ℕ, squarefreeCount n ≤ n + 1 := by
  intro n
  simpa [squarefreeCount] using
    (Finset.card_filter_le (s := Finset.range (n + 1)) (p := Squarefree))

end Submissions.Erdos969SquarefreeCountCeiling.Direct
