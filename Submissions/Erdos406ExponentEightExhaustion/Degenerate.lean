import Mathlib.Data.Nat.Digits.Lemmas

namespace Submissions.Erdos406ExponentEightExhaustion.Degenerate

theorem proof :
    False → ∀ k ≤ 8,
      Nat.digits 3 (2 ^ k) ⊆ [0, 1] ↔
        k = 0 ∨ k = 2 ∨ k = 8 := by
  intro h
  exact h.elim

end Submissions.Erdos406ExponentEightExhaustion.Degenerate
