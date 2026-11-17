import Mathlib

namespace Submissions.Erdos1041DegreeTwo.Segment

open Polynomial MeasureTheory ENNReal

/-- A monic complex quadratic with both roots in the open unit disk: the
straight segment between the two roots stays inside the unit lemniscate and
has length less than two. -/
theorem proof :
    ∀ (f : ℂ[X]), f.natDegree = 2 → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
        ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
          ∃ γ : Path z₁ z₂,
            Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
              μH[1] (Set.range γ) < 2 := by
  intro f hdeg hmonic hroots
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hcard : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hcard2 : Multiset.card f.roots = 2 := by rw [hcard, hdeg]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard2
  -- factorisation
  have hfac : (X - C a) * (X - C b) = f := by
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
    rw [hab] at h
    simpa using h
  have hev : ∀ z : ℂ, f.eval z = (z - a) * (z - b) := by
    intro z
    rw [← hfac]
    simp
  -- both roots are in the open unit disk
  have hamem : a ∈ f.roots := by
    rw [hab]
    simp
  have hbmem : b ∈ f.roots := by
    rw [hab]
    simp
  have hain : a ∈ f.rootSet ℂ := by
    refine (Polynomial.mem_rootSet_of_ne hf0).mpr ?_
    rw [Polynomial.coe_aeval_eq_eval]
    exact (Polynomial.mem_roots hf0).mp hamem
  have hbin : b ∈ f.rootSet ℂ := by
    refine (Polynomial.mem_rootSet_of_ne hf0).mpr ?_
    rw [Polynomial.coe_aeval_eq_eval]
    exact (Polynomial.mem_roots hf0).mp hbmem
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp (hroots hain)
  have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.mp (hroots hbin)
  have hd : ‖b - a‖ < 2 := by
    have h := norm_sub_le b a
    linarith
  have hd0 : 0 ≤ ‖b - a‖ := norm_nonneg _
  have hd2 : ‖b - a‖ * ‖b - a‖ < 4 := by nlinarith
  -- the straight path
  have hcont : ContinuousOn (fun t : ℝ => a + (t : ℂ) * (b - a)) unitInterval := by
    apply Continuous.continuousOn
    fun_prop
  have h0 : (fun t : ℝ => a + (t : ℂ) * (b - a)) 0 = a := by simp
  have h1 : (fun t : ℝ => a + (t : ℂ) * (b - a)) 1 = b := by simp
  have hmemimg : ∀ z ∈ Set.range (Path.ofLine hcont h0 h1),
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = a + (t : ℂ) * (b - a) := by
    intro z hz
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨t, ht, hts⟩ := Path.ofLine_mem hcont h0 h1 s
    exact ⟨t, ht.1, ht.2, hts.symm⟩
  refine ⟨a, b, le_of_eq hab.symm, Path.ofLine hcont h0 h1, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht0, ht1, rfl⟩ := hmemimg z hz
    show ‖f.eval (a + (t : ℂ) * (b - a))‖ < 1
    have hprod : (a + (t : ℂ) * (b - a) - a) * (a + (t : ℂ) * (b - a) - b)
        = ((t * (t - 1) : ℝ) : ℂ) * ((b - a) * (b - a)) := by
      push_cast
      ring
    have hnonpos : t * (t - 1) ≤ 0 := by nlinarith
    have hq : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hq0 : 0 ≤ t * (1 - t) := by nlinarith
    rw [hev, hprod, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos hnonpos]
    have hstep : -(t * (t - 1)) * (‖b - a‖ * ‖b - a‖) ≤ 1 / 4 * (‖b - a‖ * ‖b - a‖) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hd0 hd0)
      linarith
    linarith
  · have hsub : Set.range (Path.ofLine hcont h0 h1) ⊆ segment ℝ a b := by
      intro z hz
      obtain ⟨t, ht0, ht1, rfl⟩ := hmemimg z hz
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    have hmono : μH[1] (Set.range (Path.ofLine hcont h0 h1)) ≤ μH[1] (segment ℝ a b) :=
      measure_mono hsub
    have hseg : μH[1] (segment ℝ a b) = edist a b := hausdorffMeasure_segment a b
    have hdist : dist a b < 2 := by
      rw [dist_comm, dist_eq_norm]
      exact hd
    have hed : edist a b < ENNReal.ofReal 2 := edist_lt_ofReal.mpr hdist
    have htwo : ENNReal.ofReal 2 = 2 := by simp
    rw [htwo] at hed
    calc μH[1] (Set.range (Path.ofLine hcont h0 h1)) ≤ μH[1] (segment ℝ a b) := hmono
      _ = edist a b := hseg
      _ < 2 := hed

end Submissions.Erdos1041DegreeTwo.Segment
