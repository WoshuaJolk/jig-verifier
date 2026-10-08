import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.CasesM

namespace Submissions.DominoThreeCirclesAttain.Witness

theorem proof : ∃ c : Fin 3 → ℝ × ℝ,
    (∀ i, (3 - Real.sqrt 7) / 2 ≤ (c i).1 ∧ (c i).1 ≤ 1 - (3 - Real.sqrt 7) / 2 ∧
      (3 - Real.sqrt 7) / 2 ≤ (c i).2 ∧ (c i).2 ≤ 1 / 2 - (3 - Real.sqrt 7) / 2) ∧
    (∀ i j, i ≠ j → (2 * ((3 - Real.sqrt 7) / 2)) ^ 2 ≤
      ((c i).1 - (c j).1) ^ 2 + ((c i).2 - (c j).2) ^ 2) := by
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hlo : (2.6 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 7 < (2.7 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpos : (0 : ℝ) < (3 - Real.sqrt 7) / 2 := by linarith
  have hle : (3 - Real.sqrt 7) / 2 ≤ (1 : ℝ) / 4 := by linarith
  have hq : (2 * ((3 - Real.sqrt 7) / 2)) ^ 2
      = (1 / 2 - (3 - Real.sqrt 7) / 2) ^ 2 + (1 / 2 - 2 * ((3 - Real.sqrt 7) / 2)) ^ 2 := by
    nlinarith [h7]
  refine ⟨![((3 - Real.sqrt 7) / 2, (3 - Real.sqrt 7) / 2),
    (1 - (3 - Real.sqrt 7) / 2, (3 - Real.sqrt 7) / 2),
    (1 / 2, 1 / 2 - (3 - Real.sqrt 7) / 2)], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> (try constructorm* _ ∧ _) <;> nlinarith
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> nlinarith

end Submissions.DominoThreeCirclesAttain.Witness
