import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace Submissions.Erdos1135OddTwoStep.Direct

def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

theorem proof :
    ∀ n : ℕ, collatzStep (collatzStep (2 * n + 1)) = 3 * n + 2 := by
  intro n
  rw [show collatzStep (2 * n + 1) = 6 * n + 4 by
    simp [collatzStep]
    omega]
  rw [show 6 * n + 4 = 2 * (3 * n + 2) by omega]
  simp [collatzStep]

end Submissions.Erdos1135OddTwoStep.Direct
