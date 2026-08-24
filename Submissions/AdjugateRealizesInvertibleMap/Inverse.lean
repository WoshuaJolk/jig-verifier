import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic

namespace Submissions.AdjugateRealizesInvertibleMap.Inverse

open Matrix

noncomputable section

theorem proof :
    ∀ (k : ℕ) (G : Matrix (Fin k) (Fin k) ℂ), IsUnit G.det →
      ∃ (H : Matrix (Fin k) (Fin k) ℂ) (c : ℂ),
        IsUnit H.det ∧ c ≠ 0 ∧ H.adjugate = c • G := by
  intro k G hG
  let H : Matrix (Fin k) (Fin k) ℂ := G⁻¹
  have hH : IsUnit H.det := by
    exact G.isUnit_nonsing_inv_det hG
  refine ⟨H, H.det, hH, (isUnit_iff_ne_zero.mp hH), ?_⟩
  calc
    H.adjugate = 1 * H.adjugate := by rw [Matrix.one_mul]
    _ = (G * H) * H.adjugate := by
      rw [show G * H = 1 by exact G.mul_nonsing_inv hG]
    _ = G * (H * H.adjugate) := by rw [Matrix.mul_assoc]
    _ = G * (H.det • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      rw [H.mul_adjugate]
    _ = H.det • G := by rw [Matrix.mul_smul, Matrix.mul_one]

end

end Submissions.AdjugateRealizesInvertibleMap.Inverse
