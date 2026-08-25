import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Submissions.Erdos933SteinerbergerFamilyExactRatio.Worker09Upper

def twoValuation (n : ℕ) : ℕ := padicValNat 2 (n * (n + 1))

def threeValuation (n : ℕ) : ℕ := padicValNat 3 (n * (n + 1))

theorem proof :
    ∀ r : ℕ, let n := 2 ^ (3 ^ (r + 1))
      (((2 ^ twoValuation n * 3 ^ threeValuation n : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (n : ℝ))) = 3 / Real.log 2 := by
  intro r
  dsimp only
  let m := 3 ^ (r + 1)
  have hk : twoValuation (2 ^ m) = m := by
    rw [twoValuation, padicValNat.mul (by positivity) (by positivity),
      padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd
        ((Even.pow_of_ne_zero (by norm_num) (by positivity)).add_one).not_two_dvd_nat,
      add_zero]
  have hl : threeValuation (2 ^ m) = r + 2 := by
    rw [threeValuation, padicValNat.mul (by positivity) (by positivity),
      padicValNat_prime_prime_pow (p := 3) (q := 2) m (by norm_num), zero_add]
    rw [show 2 ^ m + 1 = 2 ^ m + 1 ^ m by simp,
      padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by norm_num)
        (by norm_num) (by norm_num) (by simpa [m] using (by norm_num : Odd 3).pow)]
    simp [m]
    lia
  change (((2 ^ twoValuation (2 ^ m) * 3 ^ threeValuation (2 ^ m) : ℕ) : ℝ) /
    (((2 ^ m : ℕ) : ℝ) * Real.log (((2 ^ m : ℕ) : ℝ)))) = 3 / Real.log 2
  rw [hk, hl]
  push_cast
  rw [Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  field_simp
  rw [show (3 : ℝ) ^ (r + 2) = 3 * (3 : ℝ) ^ (r + 1) by
    ring_nf]
  norm_num [m]
  ring

end Submissions.Erdos933SteinerbergerFamilyExactRatio.Worker09Upper
