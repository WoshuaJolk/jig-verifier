import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.CasesM

namespace Submissions.DominoFourCirclesAttain.Zigzag

theorem proof : ∃ c : Fin 4 → ℝ × ℝ,
    (∀ i, (11 - 6 * Real.sqrt 3) / 4 ≤ (c i).1 ∧ (c i).1 ≤ 1 - (11 - 6 * Real.sqrt 3) / 4 ∧
      (11 - 6 * Real.sqrt 3) / 4 ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - (11 - 6 * Real.sqrt 3) / 4) ∧
    (∀ i j, i ≠ j → (2 * ((11 - 6 * Real.sqrt 3) / 4)) ^ 2 ≤
      ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlo : (1.73 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 3 < (1.7321 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpos : (0 : ℝ) < (11 - 6 * Real.sqrt 3) / 4 := by linarith
  have hle : (11 - 6 * Real.sqrt 3) / 4 ≤ (1 : ℝ) / 5 := by linarith
  have hq : (2 * ((11 - 6 * Real.sqrt 3) / 4)) ^ 2
      = ((1 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) / 3) ^ 2
        + (1 / 2 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) ^ 2 := by
    nlinarith [h3]
  refine ⟨![((11 - 6 * Real.sqrt 3) / 4, (11 - 6 * Real.sqrt 3) / 4),
    ((11 - 6 * Real.sqrt 3) / 4 + (1 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) / 3,
      1 / 2 - (11 - 6 * Real.sqrt 3) / 4),
    ((11 - 6 * Real.sqrt 3) / 4 + 2 * ((1 - 2 * ((11 - 6 * Real.sqrt 3) / 4)) / 3),
      (11 - 6 * Real.sqrt 3) / 4),
    (1 - (11 - 6 * Real.sqrt 3) / 4, 1 / 2 - (11 - 6 * Real.sqrt 3) / 4)], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> (try constructorm* _ ∧ _) <;> nlinarith
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> nlinarith

end Submissions.DominoFourCirclesAttain.Zigzag
