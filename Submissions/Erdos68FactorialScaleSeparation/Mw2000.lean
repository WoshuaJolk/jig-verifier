import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68FactorialScaleSeparation.Mw2000

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

private lemma separation (y r : ℚ) (M : ℕ)
    (hM : 1 ≤ M) (hBD : y.den * r.den ≤ M.factorial) (hyr : y ≠ r) :
    ¬(|(y : ℝ) - (r : ℝ)| < (1 : ℝ) / M.factorial) := by
  have hsub0 : y - r ≠ 0 := sub_ne_zero.mpr hyr
  have hdenDvd : (y - r).den ∣ y.den * r.den := Rat.sub_den_dvd y r
  have hprodPos : 0 < y.den * r.den := Nat.mul_pos y.den_pos r.den_pos
  have hdenLeProd : (y - r).den ≤ y.den * r.den :=
    Nat.le_of_dvd hprodPos hdenDvd
  have hdenLe : (y - r).den ≤ M.factorial := hdenLeProd.trans hBD
  have hfacPos : (0 : ℝ) < M.factorial := by
    exact_mod_cast Nat.factorial_pos M
  have hdenPos : (0 : ℝ) < (y - r).den := by exact_mod_cast (y - r).den_pos
  have hrecip : (1 : ℝ) / M.factorial ≤ 1 / (y - r).den := by
    apply one_div_le_one_div_of_le hdenPos
    exact_mod_cast hdenLe
  have hsep : (1 : ℝ) / M.factorial ≤ |(y : ℝ) - (r : ℝ)| := by
    calc
      (1 : ℝ) / M.factorial ≤ 1 / (y - r).den := hrecip
      _ ≤ |((y - r : ℚ) : ℝ)| := abs_lower_by_denominator (y - r) hsub0
      _ = |(y : ℝ) - (r : ℝ)| := by norm_num
  exact not_lt.mpr hsep

theorem proof :
    (∀ y r : ℚ, ∀ M : ℕ,
      1 ≤ M →
      y.den * r.den ≤ M.factorial →
      y ≠ r →
      ¬(|(y : ℝ) - (r : ℝ)| < (1 : ℝ) / M.factorial)) ∧
    ∀ p : ℕ, p.Prime → ∀ y r : ℚ, ∀ M : ℕ,
      1 ≤ M →
      y.den * r.den ≤ M.factorial →
      |(y : ℝ) - (r : ℝ)| < (1 : ℝ) / M.factorial →
      0 ≤ padicValRat p r →
      0 ≤ padicValRat p y := by
  constructor
  · intro y r M hM hBD hyr
    exact separation y r M hM hBD hyr
  · intro p hp y r M hM hBD hclose hrval
    by_cases hyr : y = r
    · simpa [hyr] using hrval
    · have hsep := separation y r M hM hBD hyr
      exact (hsep hclose).elim

end Submissions.Erdos68FactorialScaleSeparation.Mw2000
