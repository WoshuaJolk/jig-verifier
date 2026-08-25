import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Submissions.Erdos393OddSquareReduction.Worker09Middle

def IsConsecutiveProductFactorial (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ a : ℕ, 1 ≤ a ∧ n.factorial = a * (a + 1)

theorem proof :
    ∀ n : ℕ, IsConsecutiveProductFactorial n ↔
      1 ≤ n ∧ ∃ b : ℕ, Odd b ∧ b ^ 2 = 4 * n.factorial + 1 := by
  intro n
  constructor
  · rintro ⟨hn, a, ha, hfac⟩
    refine ⟨hn, 2 * a + 1, ⟨a, by omega⟩, ?_⟩
    rw [hfac]
    ring
  · rintro ⟨hn, b, ⟨a, ha⟩, hsq⟩
    refine ⟨hn, a, ?_, ?_⟩
    · apply Nat.one_le_iff_ne_zero.mpr
      intro haz
      subst a
      simp only [mul_zero, zero_add] at ha
      subst b
      have hf := Nat.factorial_pos n
      norm_num at hsq
      omega
    · rw [ha] at hsq
      nlinarith

end Submissions.Erdos393OddSquareReduction.Worker09Middle
