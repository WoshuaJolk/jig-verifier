import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Submissions.Erdos675ZeroBoundary.Omega

def IsSumTwoSquares (m : ℕ) : Prop :=
  ∃ x y : ℕ, m = x ^ 2 + y ^ 2

theorem proof :
    ∃ t : ℕ, 1 ≤ t ∧
      ∀ a : ℕ, 1 ≤ a → a ≤ 0 →
        (IsSumTwoSquares a ↔ IsSumTwoSquares (a + t)) := by
  exact ⟨1, by norm_num, by omega⟩

end Submissions.Erdos675ZeroBoundary.Omega
