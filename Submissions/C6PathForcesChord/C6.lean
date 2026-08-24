import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

namespace Submissions.C6PathForcesChord.C6

open scoped BigOperators

noncomputable section

/-- The standard Hermitian pairing, conjugate-linear in its first argument. -/
def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

lemma pair_smul_left {k : ℕ} (z : ℂ) (x y : Fin k → ℂ) :
    pair (z • x) y = star z * pair x y := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- In dimension two, two vectors orthogonal to the same nonzero vector are
proportional. The second vector is assumed nonzero only to orient the
proportionality in the direction needed below. -/
lemma proportional_of_common_orthogonal
    {a b c : Fin 2 → ℂ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hba : pair b a = 0) (hbc : pair b c = 0) :
    ∃ z : ℂ, a = z • c := by
  simp only [pair, Fin.sum_univ_two] at hba hbc
  by_cases hb0 : b 0 = 0
  · have hb1 : b 1 ≠ 0 := by
      intro hb1
      apply hb
      funext i
      fin_cases i
      · exact hb0
      · exact hb1
    have ha1 : a 1 = 0 := by
      have h : star (b 1) * a 1 = 0 := by
        simpa only [hb0, star_zero, zero_mul, zero_add] using hba
      exact (mul_eq_zero.mp h).resolve_left (star_ne_zero.mpr hb1)
    have hc1 : c 1 = 0 := by
      have h : star (b 1) * c 1 = 0 := by
        simpa only [hb0, star_zero, zero_mul, zero_add] using hbc
      exact (mul_eq_zero.mp h).resolve_left (star_ne_zero.mpr hb1)
    have hc0 : c 0 ≠ 0 := by
      intro hc0
      apply hc
      funext i
      fin_cases i
      · exact hc0
      · exact hc1
    refine ⟨a 0 / c 0, ?_⟩
    funext i
    fin_cases i
    · simp [Pi.smul_apply, smul_eq_mul, hc0]
    · simp [Pi.smul_apply, smul_eq_mul, ha1, hc1]
  · have hstar0 : star (b 0) ≠ 0 := star_ne_zero.mpr hb0
    have hc1 : c 1 ≠ 0 := by
      intro hc1
      have hc0 : c 0 = 0 := by
        rw [hc1, mul_zero, add_zero] at hbc
        exact (mul_eq_zero.mp hbc).resolve_left hstar0
      apply hc
      funext i
      fin_cases i
      · exact hc0
      · exact hc1
    have hdet : a 0 * c 1 = c 0 * a 1 := by
      have h :
          star (b 0) * (a 0 * c 1 - c 0 * a 1) = 0 := by
        linear_combination c 1 * hba - a 1 * hbc
      have := (mul_eq_zero.mp h).resolve_left hstar0
      linear_combination this
    refine ⟨a 1 / c 1, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul]
      calc
        a 0 = c 0 * a 1 / c 1 := (eq_div_iff hc1).2 hdet
        _ = (a 1 / c 1) * c 0 := by field_simp [hc1]
    · simp [Pi.smul_apply, smul_eq_mul, hc1]

/-- The four local exactness requirements occurring on the path
`0 - 1 - 2 - 3` in `C₆` are inconsistent in `ℂ²`: the first three edges
force the non-edge `03` to be orthogonal as well. -/
theorem proof :
    ¬ ∃ v : Fin 6 → Fin 2 → ℂ,
      (∀ i, v i ≠ 0) ∧
      pair (v 1) (v 0) = 0 ∧
      pair (v 1) (v 2) = 0 ∧
      pair (v 2) (v 3) = 0 ∧
      pair (v 0) (v 3) ≠ 0 := by
  rintro ⟨v, hv, h10, h12, h23, h03⟩
  obtain ⟨z, hz⟩ :=
    proportional_of_common_orthogonal (hv 1) (hv 2) h10 h12
  apply h03
  rw [hz, pair_smul_left, h23, mul_zero]

end

end Submissions.C6PathForcesChord.C6
