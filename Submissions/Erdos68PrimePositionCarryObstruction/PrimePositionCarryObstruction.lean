import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68PrimePositionCarryObstruction.PrimePositionCarryObstruction

private lemma six_pow_lt_factorial_shift :
    ∀ t : ℕ, 6 ^ ((t + 5) / 3 + 1) < (t + 5).factorial := by
  intro t
  induction t with
  | zero => norm_num [Nat.factorial]
  | succ t ih =>
      have hdiv :
          (t + 1 + 5) / 3 + 1 ≤ ((t + 5) / 3 + 1) + 1 := by omega
      calc
        6 ^ ((t + 1 + 5) / 3 + 1)
            ≤ 6 ^ (((t + 5) / 3 + 1) + 1) :=
          Nat.pow_le_pow_right (by norm_num) hdiv
        _ = 6 ^ ((t + 5) / 3 + 1) * 6 := by rw [pow_succ]
        _ < (t + 5).factorial * 6 :=
          Nat.mul_lt_mul_of_pos_right ih (by norm_num)
        _ ≤ (t + 5).factorial * (t + 6) := by
          apply Nat.mul_le_mul_left
          omega
        _ = (t + 1 + 5).factorial := by
          conv_rhs =>
            rw [show t + 1 + 5 = (t + 5) + 1 by omega, Nat.factorial_succ]
          rw [Nat.mul_comm]

private lemma six_pow_lt_factorial {m : ℕ} (hm : 5 ≤ m) :
    6 ^ (m / 3 + 1) < m.factorial := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  simpa [Nat.add_comm] using six_pow_lt_factorial_shift t

/-- At every prime factorial position `m ≥ 5`, a single term from the `n = 3`
geometric row is assigned to a higher raw position but is already larger than
one full `1 / m!` unit. Thus the unnormalized higher-position tail cannot be
bounded below one unit at `m`. -/
theorem proof :
    ∀ m : ℕ, m.Prime → 5 ≤ m →
      let j := m / 3 + 1
      m < 3 * j ∧
        (1 : ℝ) / m.factorial < 1 / (6 : ℝ) ^ j := by
  intro m hmprime hm
  dsimp
  constructor
  · omega
  · have hpow := six_pow_lt_factorial hm
    have hpowR : (6 : ℝ) ^ (m / 3 + 1) < (m.factorial : ℝ) := by
      exact_mod_cast hpow
    have hleft : 0 < (6 : ℝ) ^ (m / 3 + 1) := by positivity
    have hright : 0 < (m.factorial : ℝ) := by positivity
    exact one_div_lt_one_div_of_lt hleft hpowR

end Submissions.Erdos68PrimePositionCarryObstruction.PrimePositionCarryObstruction
