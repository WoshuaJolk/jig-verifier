import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic

namespace Submissions.UniqueMatchingDeterminant.Leibniz

open Matrix

theorem proof :
  ∀ (n : Type) (_ : Fintype n) (_ : DecidableEq n)
    (M : Matrix n n ℂ) (σ : Equiv.Perm n),
    (∀ i, M (σ i) i ≠ 0) →
    (∀ τ : Equiv.Perm n, τ ≠ σ → ∃ i, M (τ i) i = 0) →
    M.det ≠ 0 := by
  intro n _ _ M σ hσ hunique
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single σ]
  · apply (smul_ne_zero_iff_ne _).2
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hσ i)
  · intro τ hτ hne
    obtain ⟨i, hi⟩ := hunique τ hne
    have hp : ∏ j, M (τ j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  · simp

end Submissions.UniqueMatchingDeterminant.Leibniz
