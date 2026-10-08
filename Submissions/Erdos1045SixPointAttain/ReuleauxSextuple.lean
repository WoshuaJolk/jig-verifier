import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos1045SixPointAttain.ReuleauxSextuple

/-- Vertices of the equilateral triangle of side 2 and the midpoints of the three arcs of
its Reuleaux triangle, with `s = √3`. -/
noncomputable def pts (s : ℝ) : Fin 6 → ℂ :=
  ![⟨0, 0⟩, ⟨2, 0⟩, ⟨1, s⟩, ⟨s, 1⟩, ⟨2 - s, 1⟩, ⟨1, s - 2⟩]

lemma norm_le_two (w : ℂ) (h : w.re * w.re + w.im * w.im ≤ 4) : ‖w‖ ≤ 2 := by
  have h2 : ‖w‖ ^ 2 ≤ 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; norm_num; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp h2

theorem proof :
    (64 * (2 * Real.sqrt 3 - 2) ^ 18) ∈
      ((fun z : Fin 6 → ℂ =>
        ∏ i : Fin 6, ∏ j ∈ Finset.univ.filter (fun j : Fin 6 => i < j),
          ‖z i - z j‖ ^ 2) ''
        {z : Fin 6 → ℂ | ∀ i j, ‖z i - z j‖ ≤ 2}) := by
  set s := Real.sqrt 3 with hsdef
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 3
  have hlo : 1.7 < s := by nlinarith
  have hhi : s < 1.8 := by nlinarith
  refine ⟨pts s, ?_, ?_⟩
  · intro i j
    apply norm_le_two
    fin_cases i <;> fin_cases j <;> simp [pts] <;> nlinarith
  · simp only [Complex.sq_norm, Complex.normSq_apply]
    simp [Fin.prod_univ_six, Finset.prod_filter, pts]
    linear_combination (1024*s^24 - 30720*s^23 + 446464*s^22 - 4188160*s^21 + 28538880*s^20 - 150906880*s^19 + 646787072*s^18 - 2320496640*s^17 + 7135095808*s^16 - 19058143232*s^15 + 44335177728*s^14 - 89302077440*s^13 + 154224709632*s^12 - 226043154432*s^11 + 278601621504*s^10 - 286326157312*s^9 + 243212393472*s^8 - 168926959616*s^7 + 94556590080*s^6 - 41761572864*s^5 + 14082816000*s^4 - 3430877184*s^3 + 543191040*s^2 - 43063296*s + 259072) * hs

end Submissions.Erdos1045SixPointAttain.ReuleauxSextuple
