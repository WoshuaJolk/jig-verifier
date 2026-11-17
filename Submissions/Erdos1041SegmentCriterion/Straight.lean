import Mathlib

namespace Submissions.Erdos1041SegmentCriterion.Straight

open Polynomial MeasureTheory ENNReal

/-- If the straight segment between two roots lies in the lemniscate, it is a
path of length `|a - b| < 2` joining them. -/
theorem proof :
    ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∀ a b : ℂ, ({a, b} : Multiset ℂ) ≤ f.roots →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (b - a))‖ < 1) →
        ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
          ∃ γ : Path z₁ z₂,
            Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
              μH[1] (Set.range γ) < 2 := by
  intro n f _ _ hmonic hroots a b hab hseg
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hamem : a ∈ f.roots := by
    apply Multiset.mem_of_le hab
    simp
  have hbmem : b ∈ f.roots := by
    apply Multiset.mem_of_le hab
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
  refine ⟨a, b, hab, Path.ofLine hcont h0 h1, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht0, ht1, rfl⟩ := hmemimg z hz
    exact hseg t ht0 ht1
  · have hsub : Set.range (Path.ofLine hcont h0 h1) ⊆ segment ℝ a b := by
      intro z hz
      obtain ⟨t, ht0, ht1, rfl⟩ := hmemimg z hz
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    have hmono : μH[1] (Set.range (Path.ofLine hcont h0 h1)) ≤ μH[1] (segment ℝ a b) :=
      measure_mono hsub
    have hseg' : μH[1] (segment ℝ a b) = edist a b := hausdorffMeasure_segment a b
    have hdist : dist a b < 2 := by
      rw [dist_comm, dist_eq_norm]
      exact hd
    have hed : edist a b < ENNReal.ofReal 2 := edist_lt_ofReal.mpr hdist
    have htwo : ENNReal.ofReal 2 = 2 := by simp
    rw [htwo] at hed
    calc μH[1] (Set.range (Path.ofLine hcont h0 h1)) ≤ μH[1] (segment ℝ a b) := hmono
      _ = edist a b := hseg'
      _ < 2 := hed

end Submissions.Erdos1041SegmentCriterion.Straight
