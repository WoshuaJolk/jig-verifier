import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1094NoWidthOneExceptions.Direct

theorem proof : ∀ n : ℕ,
    ¬(0 < 1 ∧ 2 * 1 ≤ n ∧
      (n.choose 1).minFac > max (n / 1) 1) := by
  intro n h
  have hn : 0 < n := by omega
  have hmin := Nat.minFac_le hn
  simp only [Nat.choose_one_right, Nat.div_one] at h
  have hmax : max n 1 = n := max_eq_left (by omega)
  rw [hmax] at h
  omega

end Submissions.Erdos1094NoWidthOneExceptions.Direct
