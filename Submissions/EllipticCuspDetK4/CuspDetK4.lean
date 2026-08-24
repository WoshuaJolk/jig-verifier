import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Submissions.EllipticCuspDetK4.CuspDetK4

@[simp] lemma sa00 : (0 : Fin 4).succAbove 0 = 1 := rfl
@[simp] lemma sa01 : (0 : Fin 4).succAbove 1 = 2 := rfl
@[simp] lemma sa02 : (0 : Fin 4).succAbove 2 = 3 := rfl
@[simp] lemma sa10 : (1 : Fin 4).succAbove 0 = 0 := rfl
@[simp] lemma sa11 : (1 : Fin 4).succAbove 1 = 2 := rfl
@[simp] lemma sa12 : (1 : Fin 4).succAbove 2 = 3 := rfl
@[simp] lemma sa20 : (2 : Fin 4).succAbove 0 = 0 := rfl
@[simp] lemma sa21 : (2 : Fin 4).succAbove 1 = 1 := rfl
@[simp] lemma sa22 : (2 : Fin 4).succAbove 2 = 3 := rfl
@[simp] lemma sa30 : (3 : Fin 4).succAbove 0 = 0 := rfl
@[simp] lemma sa31 : (3 : Fin 4).succAbove 1 = 1 := rfl
@[simp] lemma sa32 : (3 : Fin 4).succAbove 2 = 2 := rfl

def cuspMatrix (lam omega : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![0, lam^2 * omega^2, 0, 0],
    ![-lam^2 * omega^3 - lam^2 * omega^2, 0,
      -lam * omega^2 - lam, 0],
    ![0, lam * omega^3 + lam * omega^2 + lam * omega + lam, 0, 1],
    ![-lam * omega^3 - lam * omega, 0, -omega - 1, 0]
  ]

theorem proof :
    ∀ lam omega : ℂ,
      (cuspMatrix lam omega).det =
        -lam^4 * omega^3 * (omega - 1)^2 * (omega^2 + omega + 1) := by
  intro lam omega
  rw [Matrix.det_succ_row_zero]
  simp [cuspMatrix, Matrix.submatrix, Fin.sum_univ_four, Matrix.det_fin_three]
  ring

end Submissions.EllipticCuspDetK4.CuspDetK4
