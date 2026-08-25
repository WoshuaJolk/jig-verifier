import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

open scoped ArithmeticFunction.sigma

namespace Submissions.Erdos826FiniteBoxUniformBound.Elementary

theorem proof :
    ∀ N : ℕ, ∃ C > (0 : ℝ),
      ∀ n ≤ N, ∀ k ≥ 1,
        σ 0 (n + k) ≤ C * k := by
  intro N
  refine ⟨N + 1, by positivity, ?_⟩
  intro n hn k hk
  rw [ArithmeticFunction.sigma_zero_apply]
  exact_mod_cast
    (calc
      (n + k).divisors.card ≤ n + k :=
        Nat.card_divisors_le_self (n + k)
      _ ≤ N + k := Nat.add_le_add_right hn k
      _ ≤ N * k + k :=
        Nat.add_le_add_right (Nat.le_mul_of_pos_right N hk) k
      _ = (N + 1) * k := by ring)

end Submissions.Erdos826FiniteBoxUniformBound.Elementary
