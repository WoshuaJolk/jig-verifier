import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos117ExtraspecialLowerTransfer.Kernel

/-- Arithmetic/asymptotic transfer for the extraspecial lower construction.
If `h` is monotone and the odd indices satisfy `2^m ≤ h(2m+1)`, then the
constant-loss logarithmic lower estimate required by the final asymptotic
assembly holds. The group construction itself remains an external input. -/
theorem proof
    (h : ℕ → ℕ) (hmono : Monotone h)
    (hodd : ∀ m : ℕ, 2 ^ m ≤ h (2 * m + 1)) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 2 - 1 ≤ Real.logb 2 (h n : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  let m := (n - 1) / 2
  have hindex : 2 * m + 1 ≤ n := by
    dsimp [m]
    omega
  have hpow : 2 ^ m ≤ h n :=
    (hodd m).trans (hmono hindex)
  have hcast : ((2 ^ m : ℕ) : ℝ) ≤ (h n : ℝ) := by
    exact_mod_cast hpow
  have hpowPos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
    positivity
  have hhPos : (0 : ℝ) < (h n : ℝ) :=
    hpowPos.trans_le hcast
  have hlog :
      Real.logb 2 (((2 ^ m : ℕ) : ℝ)) ≤
        Real.logb 2 (h n : ℝ) :=
    (Real.strictMonoOn_logb (b := (2 : ℝ)) (by norm_num)).monotoneOn
      hpowPos hhPos hcast
  have hlog' : (m : ℝ) ≤ Real.logb 2 (h n : ℝ) := by
    simpa [Nat.cast_pow, Real.logb_pow,
      Real.logb_self_eq_one (b := (2 : ℝ)) (by norm_num)] using hlog
  have hnat : n ≤ 2 * m + 2 := by
    dsimp [m]
    omega
  have hreal : (n : ℝ) ≤ 2 * (m : ℝ) + 2 := by
    exact_mod_cast hnat
  linarith

end Submissions.Erdos117ExtraspecialLowerTransfer.Kernel
