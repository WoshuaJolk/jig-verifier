import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos676TwelveRepresentation.Worker04Smoke

theorem proof :
    ∃ p a b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ 12 = a * p ^ 2 + b := by
  exact ⟨2, 3, 0, Nat.prime_two, by norm_num⟩

end Submissions.Erdos676TwelveRepresentation.Worker04Smoke
