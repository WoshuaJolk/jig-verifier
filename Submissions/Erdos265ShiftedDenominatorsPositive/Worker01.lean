import Mathlib.Tactic

namespace Submissions.Erdos265ShiftedDenominatorsPositive.Worker01

theorem proof :
    ∀ a : ℕ → ℕ, (∀ n, 2 ≤ a n) →
      ∀ n, 0 < a n ∧ 0 < a n - 1 := by
  intro a h n
  have hn := h n
  constructor <;> omega

end Submissions.Erdos265ShiftedDenominatorsPositive.Worker01
