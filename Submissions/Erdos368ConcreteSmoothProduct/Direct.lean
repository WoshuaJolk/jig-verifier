import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Submissions.Erdos368ConcreteSmoothProduct.Direct

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

theorem proof :
    (maxPrimeFac (48 * (48 + 1)) : ℝ) <
      (Real.log (48 : ℝ)) ^ (2 + (1 : ℝ)) := by
  have hm : maxPrimeFac (48 * (48 + 1)) = 7 := by decide +kernel
  rw [hm]
  have he : Real.exp 2 < 48 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
  have hl : (2 : ℝ) < Real.log 48 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 he
  rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  have hp := pow_lt_pow_left₀ hl (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (3 : ℕ) ≠ 0)
  have h7 : (7 : ℝ) < 2 ^ (3 : ℕ) := by norm_num
  exact h7.trans hp

end Submissions.Erdos368ConcreteSmoothProduct.Direct
