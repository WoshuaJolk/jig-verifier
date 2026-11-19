import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos647HoldsAtTwentyFour.Boundary

theorem proof :
    (∀ m : ℕ, m < 24 → m + m.divisors.card ≤ 24 + 2) ∧
      ¬ (∀ m : ℕ, m < 25 → m + m.divisors.card ≤ 25 + 2) := by
  constructor
  · decide
  · intro h
    have h24 := h 24 (by norm_num)
    revert h24
    decide

end Submissions.Erdos647HoldsAtTwentyFour.Boundary
