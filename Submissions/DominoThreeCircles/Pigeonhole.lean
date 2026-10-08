import Mathlib.Analysis.Real.Sqrt

/-!
Optimality of the Packomania packing of three equal circles in `[0,1] × [0,1/2]`.

Lower bound: centres `(r, r)`, `(1 - r, r)`, `(1/2, 1/2 - r)` with `r = (3 - √7)/2`.
Upper bound (pigeonhole): two of the three centres lie on the same side of `x = 1/2`, so their
`x`-gap is at most `1/2 - r` and their `y`-gap at most `1/2 - 2r`. Hence
`4r² ≤ (1/2 - r)² + (1/2 - 2r)²`, i.e. `r² - 3r + 1/2 ≥ 0`, and with `r ≤ 1/4` this forces
`r ≤ (3 - √7)/2`.
-/

namespace Submissions.DominoThreeCircles.Pigeonhole

theorem proof : IsGreatest {r : ℝ | 0 < r ∧ ∃ c : Fin 3 → ℝ × ℝ,
    (∀ i, r ≤ (c i).1 ∧ (c i).1 ≤ 1 - r ∧ r ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - r) ∧
    (∀ i j, i ≠ j → (2 * r) ^ 2 ≤ ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2)}
    ((3 - Real.sqrt 7) / 2) := by
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hlo : (2.6 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 7 < (2.7 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor
  · -- attainment
    have hpos : (0 : ℝ) < (3 - Real.sqrt 7) / 2 := by linarith
    have hle : (3 - Real.sqrt 7) / 2 ≤ (1 : ℝ) / 4 := by linarith
    have hq : (2 * ((3 - Real.sqrt 7) / 2)) ^ 2
        = (1 / 2 - (3 - Real.sqrt 7) / 2) ^ 2 + (1 / 2 - 2 * ((3 - Real.sqrt 7) / 2)) ^ 2 := by
      nlinarith [h7]
    refine ⟨hpos, ![((3 - Real.sqrt 7) / 2, (3 - Real.sqrt 7) / 2),
      (1 - (3 - Real.sqrt 7) / 2, (3 - Real.sqrt 7) / 2),
      (1 / 2, 1 / 2 - (3 - Real.sqrt 7) / 2)], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp <;> (try constructorm* _ ∧ _) <;> nlinarith
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> nlinarith
  · -- upper bound
    intro r hr
    obtain ⟨hpos, c, hc, hd⟩ := hr
    have hr4 : r ≤ 1 / 4 := by
      have := hc 0
      linarith [this.2.2.1, this.2.2.2]
    have pair : ∀ i j : Fin 3, i ≠ j →
        (((c i).1 ≤ 1 / 2 ∧ (c j).1 ≤ 1 / 2) ∨ (1 / 2 ≤ (c i).1 ∧ 1 / 2 ≤ (c j).1)) →
        (2 * r) ^ 2 ≤ (1 / 2 - r) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by
      intro i j hij hside
      have hdij := hd i j hij
      obtain ⟨hi1, hi2, hi3, hi4⟩ := hc i
      obtain ⟨hj1, hj2, hj3, hj4⟩ := hc j
      have hx : ((c i).1 - (c j).1) ^ 2 ≤ (1 / 2 - r) ^ 2 := by
        have ha : 0 ≤ (1 / 2 - r) - ((c i).1 - (c j).1) := by
          rcases hside with h | h <;> linarith [h.1, h.2]
        have hb : 0 ≤ (1 / 2 - r) + ((c i).1 - (c j).1) := by
          rcases hside with h | h <;> linarith [h.1, h.2]
        nlinarith [mul_nonneg ha hb]
      have hy : ((c i).2 - (c j).2) ^ 2 ≤ (1 / 2 - 2 * r) ^ 2 := by
        have ha : 0 ≤ (1 / 2 - 2 * r) - ((c i).2 - (c j).2) := by linarith
        have hb : 0 ≤ (1 / 2 - 2 * r) + ((c i).2 - (c j).2) := by linarith
        nlinarith [mul_nonneg ha hb]
      linarith
    have hq : (2 * r) ^ 2 ≤ (1 / 2 - r) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by
      rcases le_total (c 0).1 (1 / 2) with h0 | h0 <;>
      rcases le_total (c 1).1 (1 / 2) with h1 | h1 <;>
      rcases le_total (c 2).1 (1 / 2) with h2 | h2 <;>
      first
        | exact pair 0 1 (by decide) (Or.inl ⟨h0, h1⟩)
        | exact pair 0 1 (by decide) (Or.inr ⟨h0, h1⟩)
        | exact pair 0 2 (by decide) (Or.inl ⟨h0, h2⟩)
        | exact pair 0 2 (by decide) (Or.inr ⟨h0, h2⟩)
        | exact pair 1 2 (by decide) (Or.inl ⟨h1, h2⟩)
        | exact pair 1 2 (by decide) (Or.inr ⟨h1, h2⟩)
    by_contra hcon
    push_neg at hcon
    have hA : 0 < r - (3 - Real.sqrt 7) / 2 := by linarith
    have hB : 0 < (3 + Real.sqrt 7) / 2 - r := by linarith
    nlinarith [mul_pos hA hB, h7]

end Submissions.DominoThreeCircles.Pigeonhole
