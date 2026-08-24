import Mathlib.Analysis.Matrix.Order

namespace Submissions.PositiveDefiniteGramFactorization.Sqrt

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

/-- A positive-definite complex matrix is the Gram matrix of an invertible
complex matrix. -/
theorem proof :
    ∀ (k : ℕ) (K : Matrix (Fin k) (Fin k) ℂ), K.PosDef →
      ∃ L : Matrix (Fin k) (Fin k) ℂ,
        IsUnit L ∧ K = L.conjTranspose * L := by
  intro k K hK
  let L : Matrix (Fin k) (Fin k) ℂ := CFC.sqrt K
  have hnonneg : 0 ≤ K := hK.posSemidef.nonneg
  have hLunit : IsUnit L := by
    exact (CFC.isUnit_sqrt_iff K hnonneg).mpr hK.isUnit
  refine ⟨L, hLunit, ?_⟩
  have hLself : L.conjTranspose = L := by
    exact (CFC.sqrt_nonneg K).isSelfAdjoint.star_eq
  calc
    K = L ^ 2 := (CFC.sq_sqrt K hnonneg).symm
    _ = L * L := by rw [pow_two]
    _ = L.conjTranspose * L := by rw [hLself]

end

end Submissions.PositiveDefiniteGramFactorization.Sqrt
