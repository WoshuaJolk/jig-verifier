import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Submissions.Erdos452SingletonOmegaInterval.Direct

def omega (n : ℕ) : ℕ := n.primeFactorsList.length

def HasOmegaRichInterval (x k : ℕ) : Prop :=
  ∃ a L : ℕ, x ≤ a ∧ a + L ≤ 2 * x + 1 ∧
    (Real.log (x : ℝ)) ^ k ≤ L ∧
      ∀ n : ℕ, a ≤ n → n < a + L →
        Real.log (Real.log (n : ℝ)) < omega n

theorem proof : HasOmegaRichInterval 3 0 := by
  refine ⟨3, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n hn3 hn4
  have hn : n = 3 := by omega
  subst n
  have he2 : (3 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hl3 : Real.log 3 < 2 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 he2
  have hll : Real.log (Real.log 3) < Real.log 2 :=
    (Real.log_lt_log_iff (Real.log_pos (by norm_num))
      (by norm_num)).2 hl3
  have hl2 : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 Real.exp_one_gt_two
  change Real.log (Real.log 3) < (omega 3 : ℝ)
  have ho : omega 3 = 1 := by decide +kernel
  rw [ho]
  norm_num
  exact hll.trans hl2

end Submissions.Erdos452SingletonOmegaInterval.Direct
