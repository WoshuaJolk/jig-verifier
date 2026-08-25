import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace Submissions.Erdos1135EvenStep.Direct

def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

theorem proof : ∀ n : ℕ, collatzStep (2 * n) = n := by
  intro n
  simp [collatzStep]

end Submissions.Erdos1135EvenStep.Direct
