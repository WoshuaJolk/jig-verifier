import Mathlib

namespace Submissions.Erdos1041SharpTwo.RealProjection

open Polynomial MeasureTheory ENNReal

/-- A path in the plane is at least as long as the gap between the real parts
of its endpoints: project to the real axis, a 1-Lipschitz map whose image is
an interval containing both real parts. -/
theorem length_ge (x y : ℂ) (γ : Path x y) :
    ENNReal.ofReal |y.re - x.re| ≤ μH[1] (Set.range γ) := by
  have hlip : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.mk_one (fun p q => ?_)
    rw [Real.dist_eq, Complex.dist_eq, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have himg := hlip.hausdorffMeasure_image_le (d := 1) zero_le_one (Set.range γ)
  have himg' : μH[1] (Complex.re '' Set.range γ) ≤ μH[1] (Set.range γ) := by
    simpa using himg
  have hpre : IsPreconnected (Complex.re '' Set.range γ) :=
    (isPreconnected_range γ.continuous).image Complex.re Complex.continuous_re.continuousOn
  have hx : x.re ∈ Complex.re '' Set.range γ := ⟨x, ⟨0, γ.source⟩, rfl⟩
  have hy : y.re ∈ Complex.re '' Set.range γ := ⟨y, ⟨1, γ.target⟩, rfl⟩
  rcases le_total x.re y.re with h | h
  · have hsub : Set.Icc x.re y.re ⊆ Complex.re '' Set.range γ := hpre.Icc_subset hx hy
    rw [abs_of_nonneg (by linarith)]
    calc ENNReal.ofReal (y.re - x.re) = volume (Set.Icc x.re y.re) := Real.volume_Icc.symm
      _ = μH[1] (Set.Icc x.re y.re) := by rw [hausdorffMeasure_real]
      _ ≤ μH[1] (Complex.re '' Set.range γ) := measure_mono hsub
      _ ≤ μH[1] (Set.range γ) := himg'
  · have hsub : Set.Icc y.re x.re ⊆ Complex.re '' Set.range γ := hpre.Icc_subset hy hx
    rw [abs_of_nonpos (by linarith), neg_sub]
    calc ENNReal.ofReal (x.re - y.re) = volume (Set.Icc y.re x.re) := Real.volume_Icc.symm
      _ = μH[1] (Set.Icc y.re x.re) := by rw [hausdorffMeasure_real]
      _ ≤ μH[1] (Complex.re '' Set.range γ) := measure_mono hsub
      _ ≤ μH[1] (Set.range γ) := himg'

/-- The quadratic with roots `±r`, `r` close to one: its two roots are `2r`
apart, so every path joining them has length at least `2r`. -/
theorem proof :
    ∀ ε : ℝ, 0 < ε → ∃ f : ℂ[X], f.natDegree = 2 ∧ f.Monic ∧
      f.rootSet ℂ ⊆ Metric.ball 0 1 ∧
      ∀ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots →
        ∀ γ : Path z₁ z₂, ENNReal.ofReal (2 - ε) ≤ μH[1] (Set.range γ) := by
  intro ε hε
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = max (1 - ε / 2) (1 / 2) := ⟨_, rfl⟩
  have hr1 : r < 1 := by
    rw [hrdef]
    exact max_lt (by linarith) (by norm_num)
  have hr0 : 0 < r := by
    have h : (1 / 2 : ℝ) ≤ r := by
      rw [hrdef]
      exact le_max_right _ _
    linarith
  have hrε : 1 - ε / 2 ≤ r := by
    rw [hrdef]
    exact le_max_left _ _
  have hmonic : ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]).Monic :=
    (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hf0 : ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]) ≠ 0 := hmonic.ne_zero
  have hroots : ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]).roots
      = ({(r : ℂ)} : Multiset ℂ) + {-(r : ℂ)} := by
    rw [Polynomial.roots_mul hf0, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  have hnorm : ∀ z : ℂ, z = (r : ℂ) ∨ z = -(r : ℂ) → ‖z‖ = r := by
    intro z hz
    rcases hz with h | h
    · rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    · rw [h, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hmemroots : ∀ z : ℂ, z ∈ ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]).roots →
      z = (r : ℂ) ∨ z = -(r : ℂ) := by
    intro z hz
    rw [hroots] at hz
    simpa using hz
  refine ⟨(X - C (r : ℂ)) * (X - C (-(r : ℂ))), ?_, hmonic, ?_, ?_⟩
  · rw [(monic_X_sub_C _).natDegree_mul (monic_X_sub_C _), natDegree_X_sub_C,
      natDegree_X_sub_C]
  · intro z hz
    have h1 := (Polynomial.mem_rootSet_of_ne hf0).mp hz
    rw [Polynomial.coe_aeval_eq_eval] at h1
    have h2 : z ∈ ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]).roots :=
      (Polynomial.mem_roots hf0).mpr h1
    rw [mem_ball_zero_iff, hnorm z (hmemroots z h2)]
    exact hr1
  · intro z₁ z₂ hle γ
    have hcardle : Multiset.card ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]).roots
        ≤ Multiset.card ({z₁, z₂} : Multiset ℂ) := by
      rw [hroots, Multiset.card_pair, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_singleton]
    have heq : ({z₁, z₂} : Multiset ℂ)
        = ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]).roots :=
      Multiset.eq_of_le_of_card_le hle hcardle
    have hsum : z₁ + z₂ = 0 := by
      have h := congrArg Multiset.sum heq
      rw [hroots] at h
      simpa using h
    have hz2 : z₂ = -z₁ := by linear_combination hsum
    have hz1mem : z₁ ∈ ((X - C (r : ℂ)) * (X - C (-(r : ℂ))) : ℂ[X]).roots := by
      apply Multiset.mem_of_le hle
      simp
    have hz1re : z₁.re = r ∨ z₁.re = -r := by
      rcases hmemroots z₁ hz1mem with h | h
      · left
        rw [h, Complex.ofReal_re]
      · right
        rw [h, Complex.neg_re, Complex.ofReal_re]
    have hz2re : z₂.re = -z₁.re := by rw [hz2, Complex.neg_re]
    have hgap : |z₂.re - z₁.re| = 2 * r := by
      rcases hz1re with h | h
      · rw [hz2re, h, abs_of_nonpos (by linarith)]
        ring
      · rw [hz2re, h, abs_of_nonneg (by linarith)]
        ring
    have hlen := length_ge z₁ z₂ γ
    rw [hgap] at hlen
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hlen

end Submissions.Erdos1041SharpTwo.RealProjection
