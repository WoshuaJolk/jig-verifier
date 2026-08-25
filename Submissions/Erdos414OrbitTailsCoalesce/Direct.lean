import Mathlib.NumberTheory.Divisors

namespace Submissions.Erdos414OrbitTailsCoalesce.Direct

def divisorStep (n : ℕ) : ℕ :=
  n + n.divisors.card

theorem proof :
    ∀ n k : ℕ, ∃ i j : ℕ,
      divisorStep^[i] n = divisorStep^[j] (divisorStep^[k] n) := by
  intro n k
  exact ⟨k, 0, rfl⟩

end Submissions.Erdos414OrbitTailsCoalesce.Direct
