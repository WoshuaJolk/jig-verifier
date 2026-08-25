import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Submissions.Erdos727CentralBinomialReduction.Direct

theorem proof :
    ∀ n k : ℕ,
      (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n) ↔
        ((n + 1).ascFactorial k) ^ 2 ∣ Nat.choose (2 * n) n := by
  intro n k
  rw [← Nat.factorial_mul_ascFactorial n k]
  have hchoose :
      Nat.choose (2 * n) n * Nat.factorial n * Nat.factorial n =
        Nat.factorial (2 * n) := by
    simpa [two_mul] using
      (Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega))
  rw [← hchoose]
  simp only [pow_two]
  rw [show
      (Nat.factorial n * (n + 1).ascFactorial k) *
          (Nat.factorial n * (n + 1).ascFactorial k) =
        (Nat.factorial n * Nat.factorial n) *
          ((n + 1).ascFactorial k * (n + 1).ascFactorial k) by ac_rfl]
  rw [show
      Nat.choose (2 * n) n * Nat.factorial n * Nat.factorial n =
        (Nat.factorial n * Nat.factorial n) * Nat.choose (2 * n) n by ac_rfl]
  exact mul_dvd_mul_iff_left
    (Nat.mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero n))

end Submissions.Erdos727CentralBinomialReduction.Direct
