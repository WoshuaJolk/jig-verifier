import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68SmallTailDenExceedsFactorial.Mw2000

private lemma abs_lower_by_denominator (q : ℚ) (hq : q ≠ 0) :
    (1 : ℝ) / q.den ≤ |(q : ℝ)| := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hnumAbs : (1 : ℝ) ≤ |(q.num : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hnum)
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hqcast : (q : ℝ) = (q.num : ℝ) / q.den := by
    exact_mod_cast q.num_div_den.symm
  rw [hqcast, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right hnumAbs hden.le

private lemma den_gt_factorial {y : ℚ} {M : ℕ}
    (hy : 0 < y) (hsmall : (y : ℝ) < (1 : ℝ) / M.factorial) :
    M.factorial < y.den := by
  have hy0 : y ≠ 0 := hy.ne'
  have hdenPos : (0 : ℝ) < y.den := by exact_mod_cast y.den_pos
  have hfacPos : (0 : ℝ) < M.factorial := by
    exact_mod_cast Nat.factorial_pos M
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have habs : |(y : ℝ)| = y := abs_of_pos hyR
  have hle : (1 : ℝ) / y.den ≤ (y : ℝ) := by
    simpa [habs] using abs_lower_by_denominator y hy0
  have hstrict : (1 : ℝ) / y.den < (1 : ℝ) / M.factorial :=
    hle.trans_lt hsmall
  have : (M.factorial : ℝ) < y.den :=
    (one_div_lt_one_div hdenPos hfacPos).mp hstrict
  exact_mod_cast this

theorem proof :
    ∀ y r : ℚ, ∀ M : ℕ,
      1 ≤ M →
      0 < y →
      (y : ℝ) < (1 : ℝ) / M.factorial →
      M.factorial < y.den * r.den := by
  intro y r M _hM hy hsmall
  have hden : M.factorial < y.den := den_gt_factorial hy hsmall
  have hr : 1 ≤ r.den := Nat.succ_le_of_lt r.den_pos
  have : y.den * 1 ≤ y.den * r.den :=
    Nat.mul_le_mul_left y.den hr
  have h' : M.factorial < y.den * 1 := by simpa using hden
  exact h'.trans_le this

end Submissions.Erdos68SmallTailDenExceedsFactorial.Mw2000
