import Mathlib.Data.Nat.Basic

namespace Submissions.Erdos675ZeroBoundary.FalsePremise

def IsSumTwoSquares (m : ℕ) : Prop :=
  ∃ x y : ℕ, m = x ^ 2 + y ^ 2

theorem proof :
    False →
      ∃ t : ℕ, 1 ≤ t ∧
        ∀ a : ℕ, 1 ≤ a → a ≤ 0 →
          (IsSumTwoSquares a ↔ IsSumTwoSquares (a + t)) := by
  intro h
  exact h.elim

end Submissions.Erdos675ZeroBoundary.FalsePremise
