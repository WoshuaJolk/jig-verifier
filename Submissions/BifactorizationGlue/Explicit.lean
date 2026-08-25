import Mathlib

namespace Submissions.BifactorizationGlue.Explicit

open scoped BigOperators

universe u v w

theorem proof
    {ι : Type u} {κ : Type v} {ϕ : Type w}
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ϕ ℂ)
    (D : Matrix ι κ ℂ) (X : Matrix κ ϕ ℂ)
    (C : Matrix ι ϕ ℂ)
    (f : κ → ι) (g : κ → ϕ)
    (hAB : C = A * B) (hDX : C = D * X)
    (hdet : (C.submatrix f g).det ≠ 0) :
    ∃ G : Matrix κ κ ℂ, G.det ≠ 0 ∧ C = A * (G * X) := by
  let Ar : Matrix κ κ ℂ := A.submatrix f id
  let Bs : Matrix κ κ ℂ := B.submatrix id g
  let Dr : Matrix κ κ ℂ := D.submatrix f id
  let Xs : Matrix κ κ ℂ := X.submatrix id g
  have hCselAB : C.submatrix f g = Ar * Bs := by
    rw [hAB]
    ext a b
    simp [Ar, Bs, Matrix.mul_apply]
  have hCselDX : C.submatrix f g = Dr * Xs := by
    rw [hDX]
    ext a b
    simp [Dr, Xs, Matrix.mul_apply]
  have hprodAB : Ar.det * Bs.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hCselAB]
    exact hdet
  have hprodDX : Dr.det * Xs.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hCselDX]
    exact hdet
  have hAr : IsUnit Ar.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodAB).1
  have hBs : IsUnit Bs.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodAB).2
  have hXs : IsUnit Xs.det :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hprodDX).2
  have hrows : Ar * B = Dr * X := by
    ext a j
    have hij := congrArg (fun M : Matrix ι ϕ ℂ => M (f a) j)
      (hAB.symm.trans hDX)
    simpa [Ar, Dr, Matrix.mul_apply] using hij
  have hselected : Ar * Bs = Dr * Xs := hCselAB.symm.trans hCselDX
  let G : Matrix κ κ ℂ := Bs * Xs⁻¹
  have hArG : Ar * G = Dr := by
    calc
      Ar * G = (Ar * Bs) * Xs⁻¹ := by simp [G, Matrix.mul_assoc]
      _ = (Dr * Xs) * Xs⁻¹ := by rw [hselected]
      _ = Dr := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Xs hXs, Matrix.mul_one]
  have hArEq : Ar * (G * X) = Ar * B := by
    calc
      Ar * (G * X) = (Ar * G) * X := (Matrix.mul_assoc Ar G X).symm
      _ = Dr * X := by rw [hArG]
      _ = Ar * B := hrows.symm
  have hB : G * X = B := by
    have hmul := congrArg (fun M : Matrix κ ϕ ℂ => Ar⁻¹ * M) hArEq
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Ar hAr] using hmul
  have hGunit : IsUnit G.det := by
    change IsUnit (Bs * Xs⁻¹).det
    rw [Matrix.det_mul]
    exact hBs.mul (Matrix.isUnit_nonsing_inv_det Xs hXs)
  refine ⟨G, isUnit_iff_ne_zero.mp hGunit, ?_⟩
  calc
    C = A * B := hAB
    _ = A * (G * X) := congrArg (fun Y : Matrix κ ϕ ℂ => A * Y) hB.symm

end Submissions.BifactorizationGlue.Explicit
