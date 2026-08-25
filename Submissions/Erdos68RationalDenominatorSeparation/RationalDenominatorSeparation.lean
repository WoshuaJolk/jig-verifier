import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68RationalDenominatorSeparation.RationalDenominatorSeparation

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

private theorem separation :
    ∀ y r : ℚ, ∀ B D : ℕ,
      y.den ≤ B → r.den ≤ D → y ≠ r →
      (1 : ℝ) / (B * D) ≤ |(y : ℝ) - (r : ℝ)| := by
  intro y r B D hyB hrD hyr
  have hsub0 : y - r ≠ 0 := sub_ne_zero.mpr hyr
  have hdenDvd : (y - r).den ∣ y.den * r.den :=
    Rat.sub_den_dvd y r
  have hprodPos : 0 < y.den * r.den :=
    Nat.mul_pos y.den_pos r.den_pos
  have hdenLeProd : (y - r).den ≤ y.den * r.den :=
    Nat.le_of_dvd hprodPos hdenDvd
  have hdenLe : (y - r).den ≤ B * D :=
    hdenLeProd.trans (Nat.mul_le_mul hyB hrD)
  have hBDpos : 0 < B * D := by
    have hB : 0 < B := lt_of_lt_of_le y.den_pos hyB
    have hD : 0 < D := lt_of_lt_of_le r.den_pos hrD
    exact Nat.mul_pos hB hD
  have hrecip :
      (1 : ℝ) / (B * D) ≤ 1 / (y - r).den := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast (y - r).den_pos
    · exact_mod_cast hdenLe
  calc
    (1 : ℝ) / (B * D) ≤ 1 / (y - r).den := hrecip
    _ ≤ |((y - r : ℚ) : ℝ)| :=
      abs_lower_by_denominator (y - r) hsub0
    _ = |(y : ℝ) - (r : ℝ)| := by norm_num

/-- Two distinct rationals whose reduced denominators are bounded by `B` and
`D` are separated in the real metric by at least `1/(BD)`. Consequently, a
closer `p`-integral finite approximant forces the rational limit itself to be
`p`-integral. -/
theorem proof :
    (∀ y r : ℚ, ∀ B D : ℕ,
      y.den ≤ B → r.den ≤ D → y ≠ r →
      (1 : ℝ) / (B * D) ≤ |(y : ℝ) - (r : ℝ)|) ∧
    ∀ p : ℕ, p.Prime → ∀ y r : ℚ, ∀ B D : ℕ,
      y.den ≤ B → r.den ≤ D →
      |(y : ℝ) - (r : ℝ)| < (1 : ℝ) / (B * D) →
      0 ≤ padicValRat p r →
      0 ≤ padicValRat p y := by
  constructor
  · exact separation
  · intro p hp y r B D hyB hrD hclose hrval
    by_cases hyr : y = r
    · simpa [hyr] using hrval
    · have hsep := separation y r B D hyB hrD hyr
      linarith

end Submissions.Erdos68RationalDenominatorSeparation.RationalDenominatorSeparation
