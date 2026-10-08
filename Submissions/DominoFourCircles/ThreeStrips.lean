import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.CasesM

/-!
Optimality of the Packomania packing of four equal circles in `[0,1] × [0,1/2]`.

Lower bound: zigzag centres `(r + k a/3, y_k)` for `k = 0..3`, `a = 1 - 2r`, with `y_k`
alternating `r`, `1/2 - r`, and `r = (11 - 6√3)/4`.
Upper bound (pigeonhole): cut the centre range `[r, 1 - r]` into three closed strips of width
`a/3`. Two of the four centres share a strip, so their `x`-gap is at most `a/3` and their
`y`-gap at most `1/2 - 2r`. Hence `4r² ≤ (a/3)² + (1/2 - 2r)²`, i.e.
`r² - (11/2) r + 13/16 ≥ 0`, and with `r ≤ 1/4` this forces `r ≤ (11 - 6√3)/4`.
-/

namespace Submissions.DominoFourCircles.ThreeStrips

theorem proof : IsGreatest {r : ℝ | 0 < r ∧ ∃ c : Fin 4 → ℝ × ℝ,
    (∀ i, r ≤ (c i).1 ∧ (c i).1 ≤ 1 - r ∧ r ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - r) ∧
    (∀ i j, i ≠ j → (2 * r) ^ 2 ≤ ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2)}
    ((11 - 6 * Real.sqrt 3) / 4) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlo : (1.73 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 3 < (1.7321 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor
  · -- attainment
    have hpos : (0 : ℝ) < (11 - 6 * Real.sqrt 3) / 4 := by linarith
    have hle : (11 - 6 * Real.sqrt 3) / 4 ≤ (1 : ℝ) / 5 := by linarith
    have hq : (2 * ((11 - 6 * Real.sqrt 3) / 4)) ^ 2
        = ((1 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) / 3) ^ 2
          + (1 / 2 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) ^ 2 := by
      nlinarith [h3]
    refine ⟨hpos, ![((11 - 6 * Real.sqrt 3) / 4, (11 - 6 * Real.sqrt 3) / 4),
      ((11 - 6 * Real.sqrt 3) / 4 + (1 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) / 3,
        1 / 2 - (11 - 6 * Real.sqrt 3) / 4),
      ((11 - 6 * Real.sqrt 3) / 4 + 2 * ((1 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) / 3),
        (11 - 6 * Real.sqrt 3) / 4),
      (1 - (11 - 6 * Real.sqrt 3) / 4, 1 / 2 - (11 - 6 * Real.sqrt 3) / 4)], ?_, ?_⟩
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
    -- two centres in a common strip `[lo, lo + (1 - 2r)/3]` force the key inequality
    have pair : ∀ i j : Fin 4, i ≠ j → ∀ lo : ℝ,
        lo ≤ (c i).1 → (c i).1 ≤ lo + (1 - 2 * r) / 3 →
        lo ≤ (c j).1 → (c j).1 ≤ lo + (1 - 2 * r) / 3 →
        (2 * r) ^ 2 ≤ ((1 - 2 * r) / 3) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by
      intro i j hij lo hi1 hi2 hj1 hj2
      have hdij := hd i j hij
      obtain ⟨-, -, hi3, hi4⟩ := hc i
      obtain ⟨-, -, hj3, hj4⟩ := hc j
      have hx : ((c i).1 - (c j).1) ^ 2 ≤ ((1 - 2 * r) / 3) ^ 2 := by
        have ha : 0 ≤ (1 - 2 * r) / 3 - ((c i).1 - (c j).1) := by linarith
        have hb : 0 ≤ (1 - 2 * r) / 3 + ((c i).1 - (c j).1) := by linarith
        nlinarith [mul_nonneg ha hb]
      have hy : ((c i).2 - (c j).2) ^ 2 ≤ (1 / 2 - 2 * r) ^ 2 := by
        have ha : 0 ≤ (1 / 2 - 2 * r) - ((c i).2 - (c j).2) := by linarith
        have hb : 0 ≤ (1 / 2 - 2 * r) + ((c i).2 - (c j).2) := by linarith
        nlinarith [mul_nonneg ha hb]
      linarith
    -- the three strips
    have s0 : ∀ i j : Fin 4, i ≠ j → (c i).1 ≤ r + (1 - 2 * r) / 3 →
        (c j).1 ≤ r + (1 - 2 * r) / 3 →
        (2 * r) ^ 2 ≤ ((1 - 2 * r) / 3) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by
      intro i j hij hi hj
      exact pair i j hij r (hc i).1 hi (hc j).1 hj
    have s1 : ∀ i j : Fin 4, i ≠ j →
        (r + (1 - 2 * r) / 3 ≤ (c i).1 ∧ (c i).1 ≤ r + 2 * ((1 - 2 * r) / 3)) →
        (r + (1 - 2 * r) / 3 ≤ (c j).1 ∧ (c j).1 ≤ r + 2 * ((1 - 2 * r) / 3)) →
        (2 * r) ^ 2 ≤ ((1 - 2 * r) / 3) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by
      intro i j hij hi hj
      exact pair i j hij (r + (1 - 2 * r) / 3) hi.1 (by linarith [hi.2]) hj.1 (by linarith [hj.2])
    have s2 : ∀ i j : Fin 4, i ≠ j → r + 2 * ((1 - 2 * r) / 3) ≤ (c i).1 →
        r + 2 * ((1 - 2 * r) / 3) ≤ (c j).1 →
        (2 * r) ^ 2 ≤ ((1 - 2 * r) / 3) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by
      intro i j hij hi hj
      exact pair i j hij (r + 2 * ((1 - 2 * r) / 3)) hi (by linarith [(hc i).2.1])
        hj (by linarith [(hc j).2.1])
    have tri : ∀ i : Fin 4, (c i).1 ≤ r + (1 - 2 * r) / 3 ∨
        (r + (1 - 2 * r) / 3 ≤ (c i).1 ∧ (c i).1 ≤ r + 2 * ((1 - 2 * r) / 3)) ∨
        r + 2 * ((1 - 2 * r) / 3) ≤ (c i).1 := by
      intro i
      rcases le_total ((c i).1) (r + (1 - 2 * r) / 3) with h | h
      · exact Or.inl h
      · rcases le_total ((c i).1) (r + 2 * ((1 - 2 * r) / 3)) with h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr h')
    have hq : (2 * r) ^ 2 ≤ ((1 - 2 * r) / 3) ^ 2 + (1 / 2 - 2 * r) ^ 2 := by
      rcases tri 0 with h0 | h0 | h0 <;>
      rcases tri 1 with h1 | h1 | h1 <;>
      rcases tri 2 with h2 | h2 | h2 <;>
      rcases tri 3 with h3' | h3' | h3' <;>
      first
        | exact s0 0 1 (by decide) h0 h1 | exact s1 0 1 (by decide) h0 h1
        | exact s2 0 1 (by decide) h0 h1
        | exact s0 0 2 (by decide) h0 h2 | exact s1 0 2 (by decide) h0 h2
        | exact s2 0 2 (by decide) h0 h2
        | exact s0 0 3 (by decide) h0 h3' | exact s1 0 3 (by decide) h0 h3'
        | exact s2 0 3 (by decide) h0 h3'
        | exact s0 1 2 (by decide) h1 h2 | exact s1 1 2 (by decide) h1 h2
        | exact s2 1 2 (by decide) h1 h2
        | exact s0 1 3 (by decide) h1 h3' | exact s1 1 3 (by decide) h1 h3'
        | exact s2 1 3 (by decide) h1 h3'
        | exact s0 2 3 (by decide) h2 h3' | exact s1 2 3 (by decide) h2 h3'
        | exact s2 2 3 (by decide) h2 h3'
    by_contra hcon0
    have hcon := not_le.mp hcon0
    have hA : 0 < r - (11 - 6 * Real.sqrt 3) / 4 := by linarith
    have hB : 0 < (11 + 6 * Real.sqrt 3) / 4 - r := by linarith
    nlinarith [mul_pos hA hB, h3]

end Submissions.DominoFourCircles.ThreeStrips
