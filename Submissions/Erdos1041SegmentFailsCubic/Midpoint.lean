import Mathlib

namespace Submissions.Erdos1041SegmentFailsCubic.Midpoint

open Polynomial

/-- For `z ^ 3 - 9/10` the midpoint of two distinct roots has value `-81/80`. -/
theorem proof :
    ∃ f : ℂ[X], f.natDegree = 3 ∧ f.Monic ∧ f.rootSet ℂ ⊆ Metric.ball 0 1 ∧
      ∀ a b : ℂ, a ∈ f.roots → b ∈ f.roots → a ≠ b →
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 1 ≤ ‖f.eval (a + (t : ℂ) * (b - a))‖ := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = (((9 / 10 : ℝ)) : ℂ) := ⟨_, rfl⟩
  have hcnorm : ‖c‖ = 9 / 10 := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  obtain ⟨f, hfdef⟩ : ∃ f : ℂ[X], f = X ^ 3 - C c := ⟨_, rfl⟩
  have hnat : f.natDegree = 3 := by
    rw [hfdef]
    exact natDegree_X_pow_sub_C
  have hmonic : f.Monic := by
    rw [hfdef]
    exact monic_X_pow_sub_C c (by norm_num)
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have heval : ∀ z : ℂ, f.eval z = z ^ 3 - c := by
    intro z
    rw [hfdef]
    simp
  have hrootpow : ∀ z ∈ f.roots, z ^ 3 = c := by
    intro z hz
    have h : f.eval z = 0 := (Polynomial.mem_roots hf0).mp hz
    rw [heval] at h
    exact sub_eq_zero.mp h
  have hrootnorm : ∀ z ∈ f.roots, ‖z‖ < 1 := by
    intro z hz
    by_contra hge
    have h1 : 1 ≤ ‖z‖ := not_lt.mp hge
    have h2 : (1 : ℝ) ≤ ‖z‖ ^ 3 := one_le_pow₀ h1
    have h3 : ‖z‖ ^ 3 = ‖c‖ := by rw [← norm_pow, hrootpow z hz]
    rw [hcnorm] at h3
    linarith
  have hsub : f.rootSet ℂ ⊆ Metric.ball 0 1 := by
    intro z hz
    have hz1 := (Polynomial.mem_rootSet_of_ne hf0).mp hz
    rw [Polynomial.coe_aeval_eq_eval] at hz1
    exact mem_ball_zero_iff.mpr (hrootnorm z ((Polynomial.mem_roots hf0).mpr hz1))
  refine ⟨f, hnat, hmonic, hsub, ?_⟩
  intro a b ha hb hab
  have han : a ^ 3 = c := hrootpow a ha
  have hbn : b ^ 3 = c := hrootpow b hb
  have hmul : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by
    linear_combination han - hbn
  have hquad : a ^ 2 + a * b + b ^ 2 = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · exact h
  have hE : (a + (((1 / 2 : ℝ)) : ℂ) * (b - a)) ^ 3 - c = (((-(9 / 8) : ℝ)) : ℂ) * c := by
    push_cast
    linear_combination (1 / 8 : ℂ) * han - (2 / 8 : ℂ) * hbn + (3 / 8 : ℂ) * b * hquad
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  rw [heval, hE, norm_mul, Complex.norm_real, Real.norm_eq_abs, hcnorm, abs_neg,
    abs_of_pos (by norm_num)]
  norm_num

end Submissions.Erdos1041SegmentFailsCubic.Midpoint
