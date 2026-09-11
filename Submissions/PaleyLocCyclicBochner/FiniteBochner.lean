import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite Bochner extraction for a real PSD circulant on `ZMod n`.
Character orthogonality follows the finite-sum argument in Mathlib's
`Analysis/Fourier/ZMod.lean` (David Loeffler, Apache 2.0).
-/

open Finset AddChar Matrix

namespace Submissions.PaleyLocCyclicBochner.FiniteBochner

variable {n : ℕ} [NeZero n]

private lemma character_sum (t : ZMod n) :
    ∑ j : ZMod n, ZMod.stdAddChar (t * j) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

omit [NeZero n] in
private lemma even_of_psd {f : ZMod n → ℝ} (hf : (Matrix.circulant f).PosSemidef) :
    ∀ t, f (-t) = f t := by
  exact Matrix.circulant_isSymm_iff.mp (Matrix.isHermitian_iff_isSymm.mp hf.1)

private noncomputable def coefficient (f : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  ∑ t, f t * (ZMod.stdAddChar (t * j)).re

private lemma coefficient_complex {f : ZMod n → ℝ} (he : ∀ t, f (-t) = f t)
    (j : ZMod n) :
    (coefficient f j : ℂ) = ∑ t, (f t : ℂ) * ZMod.stdAddChar (-(t * j)) := by
  have him : ∑ t : ZMod n, f t * (ZMod.stdAddChar (t * j)).im = 0 := by
    have h := Fintype.sum_equiv (Equiv.neg (ZMod n))
      (fun t => f t * (ZMod.stdAddChar (t * j)).im)
      (fun t => -(f t * (ZMod.stdAddChar (t * j)).im))
      (fun t => by simp [he, neg_mul, AddChar.map_neg_eq_conj])
    simp only [sum_neg_distrib] at h
    linarith
  apply Complex.ext
  · simp [coefficient, AddChar.map_neg_eq_conj]
  · simpa [AddChar.map_neg_eq_conj] using him

private lemma coefficient_nonneg {f : ZMod n → ℝ}
    (hf : (Matrix.circulant f).PosSemidef) (j : ZMod n) : 0 ≤ coefficient f j := by
  let r : ZMod n → ℝ := fun t => (ZMod.stdAddChar (t * j)).re
  let s : ZMod n → ℝ := fun t => (ZMod.stdAddChar (t * j)).im
  have hr := hf.dotProduct_mulVec_nonneg r
  have hs := hf.dotProduct_mulVec_nonneg s
  have hchar (u v : ZMod n) :
      r u * r v + s u * s v = (ZMod.stdAddChar ((u-v)*j)).re := by
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
    simp [r, s, Complex.mul_re]
  have hquad : star r ⬝ᵥ (Matrix.circulant f *ᵥ r) +
      star s ⬝ᵥ (Matrix.circulant f *ᵥ s) = (n : ℝ) * coefficient f j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.circulant_apply, Pi.star_apply,
      star_trivial, mul_sum, ← sum_add_distrib]
    calc
      _ = ∑ u : ZMod n, ∑ v : ZMod n,
          f (u-v) * (ZMod.stdAddChar ((u-v)*j)).re := by
        apply sum_congr rfl
        intro u _
        apply sum_congr rfl
        intro v _
        rw [← hchar]
        ring
      _ = ∑ v : ZMod n, coefficient f j := by
        rw [sum_comm]
        apply sum_congr rfl
        intro v _
        exact Fintype.sum_equiv (Equiv.subRight v) _ _ (fun u => rfl)
      _ = (n : ℝ) * coefficient f j := by simp [ZMod.card]
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  exact (mul_nonneg_iff_of_pos_left hn).mp (hquad ▸ add_nonneg hr hs)

private lemma coefficient_inversion {f : ZMod n → ℝ} (he : ∀ t, f (-t) = f t)
    (t : ZMod n) :
    ∑ j : ZMod n, (coefficient f j : ℂ) * ZMod.stdAddChar (j*t) =
      (n : ℂ) * (f t : ℂ) := by
  simp only [coefficient_complex he, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ u : ZMod n, (f u : ℂ) * ∑ j : ZMod n,
        ZMod.stdAddChar ((t-u)*j) := by
      apply sum_congr rfl
      intro u _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (n : ℂ) * (f t : ℂ) := by
      simp only [character_sum]
      simp [sub_eq_zero, mul_comm]

/-- A normalized real PSD circulant is a probability mixture of the standard
characters. Its sum is the group order times the trivial-character mass. -/
theorem proof {f : ZMod n → ℝ}
    (hf : (Matrix.circulant f).PosSemidef) (hzero : f 0 = 1) :
    ∃ μ : ZMod n → ℝ,
      (∀ j, 0 ≤ μ j) ∧
      (∑ j, μ j) = 1 ∧
      (∀ t, (f t : ℂ) = ∑ j, (μ j : ℂ) * ZMod.stdAddChar (j*t)) ∧
      (∑ t, f t) = (n : ℝ) * μ 0 := by
  let μ : ZMod n → ℝ := fun j => coefficient f j / (n : ℝ)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hinv (t : ZMod n) :
      (f t : ℂ) = ∑ j, (μ j : ℂ) * ZMod.stdAddChar (j*t) := by
    simp only [μ, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast]
    calc
      _ = (n : ℂ)⁻¹ * ((n : ℂ) * (f t : ℂ)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hnc, one_mul]
      _ = (n : ℂ)⁻¹ * ∑ j, (coefficient f j : ℂ) * ZMod.stdAddChar (j*t) := by
        rw [coefficient_inversion (even_of_psd hf)]
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
  refine ⟨μ, fun j => div_nonneg (coefficient_nonneg hf j) (Nat.cast_nonneg n), ?_,
    hinv, ?_⟩
  · have h := congrArg Complex.re (hinv 0)
    simpa [hzero] using h.symm
  · simp only [μ, coefficient, mul_zero, AddChar.map_zero_eq_one, Complex.one_re,
      mul_one]
    exact (mul_div_cancel₀ _ hn).symm

end Submissions.PaleyLocCyclicBochner.FiniteBochner
