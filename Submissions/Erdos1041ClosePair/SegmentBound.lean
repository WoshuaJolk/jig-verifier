import Mathlib

namespace Submissions.Erdos1041ClosePair.SegmentBound

open Polynomial MeasureTheory ENNReal

/-- A product of factors `z - r`, each of modulus at most two. -/
theorem norm_prod_le (z : ℂ) (s : Multiset ℂ) (h : ∀ r ∈ s, ‖z - r‖ ≤ 2) :
    ‖(s.map (fun r => z - r)).prod‖ ≤ 2 ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have h1 : ‖z - x‖ ≤ 2 := h x (Multiset.mem_cons_self x s)
    have h2 : ‖(s.map (fun r => z - r)).prod‖ ≤ 2 ^ Multiset.card s :=
      ih (fun r hr => h r (Multiset.mem_cons_of_mem hr))
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    calc ‖z - x‖ * ‖(s.map (fun r => z - r)).prod‖
        ≤ 2 * 2 ^ Multiset.card s := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 2 ^ Multiset.card s * 2 := mul_comm _ _

/-- Two roots at distance `d` with `d² · 2^(n-2) < 4`: on the segment between
them the two near factors contribute at most `d²/4` and each other factor at
most two. -/
theorem proof :
    ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∀ a b : ℂ, ({a, b} : Multiset ℂ) ≤ f.roots →
      ‖a - b‖ ^ 2 * 2 ^ (n - 2) < 4 →
        ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
          ∃ γ : Path z₁ z₂,
            Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
              μH[1] (Set.range γ) < 2 := by
  intro n f hn2 hdeg hmonic hroots a b hab hclose
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
  -- the estimate on the segment
  have hcard : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac : (f.roots.map (fun r => X - C r)).prod = f :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  obtain ⟨rest, hrest⟩ := Multiset.le_iff_exists_add.mp hab
  have hcrest : Multiset.card rest = n - 2 := by
    have h := congrArg Multiset.card hrest
    rw [Multiset.card_add, Multiset.card_pair, hcard, hdeg] at h
    omega
  have hev : ∀ z : ℂ, f.eval z = (z - a) * (z - b) * (rest.map (fun r => z - r)).prod := by
    intro z
    have h := congrArg (Polynomial.eval z) hfac
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, hrest, Multiset.map_add,
      Multiset.prod_add] at h
    rw [← h]
    congr 1
    · simp
    · congr 1
      apply Multiset.map_congr rfl
      intro r _
      simp
  have hrestmem : ∀ r ∈ rest, ‖r‖ < 1 := by
    intro r hr
    have hrmem : r ∈ f.roots := by
      rw [hrest]
      exact Multiset.mem_add.mpr (Or.inr hr)
    have hrin : r ∈ f.rootSet ℂ := by
      refine (Polynomial.mem_rootSet_of_ne hf0).mpr ?_
      rw [Polynomial.coe_aeval_eq_eval]
      exact (Polynomial.mem_roots hf0).mp hrmem
    exact mem_ball_zero_iff.mp (hroots hrin)
  have hD : ‖b - a‖ * ‖b - a‖ * 2 ^ (n - 2) < 4 := by
    have h := hclose
    rw [norm_sub_rev, sq] at h
    exact h
  have hd0 : 0 ≤ ‖b - a‖ := norm_nonneg _
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (b - a))‖ < 1 := by
    intro t ht0 ht1
    have hzform : a + (t : ℂ) * (b - a) = ((1 - t : ℝ) : ℂ) * a + (t : ℂ) * b := by
      push_cast
      ring
    have hznorm : ‖a + (t : ℂ) * (b - a)‖ ≤ 1 := by
      rw [hzform]
      have h := norm_add_le (((1 - t : ℝ) : ℂ) * a) ((t : ℂ) * b)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), abs_of_nonneg ht0] at h
      have e1 : 0 ≤ (1 - t) * (1 - ‖a‖) := mul_nonneg (by linarith) (by linarith)
      have e2 : 0 ≤ t * (1 - ‖b‖) := mul_nonneg ht0 (by linarith)
      nlinarith [e1, e2]
    have hfactors : ∀ r ∈ rest, ‖a + (t : ℂ) * (b - a) - r‖ ≤ 2 := by
      intro r hr
      have h := norm_sub_le (a + (t : ℂ) * (b - a)) r
      have h' := hrestmem r hr
      linarith
    have hP := norm_prod_le (a + (t : ℂ) * (b - a)) rest hfactors
    rw [hcrest] at hP
    have hprod : (a + (t : ℂ) * (b - a) - a) * (a + (t : ℂ) * (b - a) - b)
        = ((t * (t - 1) : ℝ) : ℂ) * ((b - a) * (b - a)) := by
      push_cast
      ring
    have hnonpos : t * (t - 1) ≤ 0 := by nlinarith
    have hq : -(t * (t - 1)) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hq0 : 0 ≤ -(t * (t - 1)) := by linarith
    rw [hev, hprod, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos hnonpos]
    have hstep1 : -(t * (t - 1)) * (‖b - a‖ * ‖b - a‖) ≤ 1 / 4 * (‖b - a‖ * ‖b - a‖) :=
      mul_le_mul_of_nonneg_right hq (mul_nonneg hd0 hd0)
    have hstep2 : -(t * (t - 1)) * (‖b - a‖ * ‖b - a‖)
          * ‖(rest.map (fun r => a + (t : ℂ) * (b - a) - r)).prod‖
        ≤ 1 / 4 * (‖b - a‖ * ‖b - a‖) * 2 ^ (n - 2) :=
      mul_le_mul hstep1 hP (norm_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg hd0 hd0))
    have hfin : 1 / 4 * (‖b - a‖ * ‖b - a‖) * (2 : ℝ) ^ (n - 2) < 1 := by
      have e : 1 / 4 * (‖b - a‖ * ‖b - a‖) * (2 : ℝ) ^ (n - 2)
          = (‖b - a‖ * ‖b - a‖ * 2 ^ (n - 2)) / 4 := by ring
      rw [e]
      linarith
    exact lt_of_le_of_lt hstep2 hfin
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

end Submissions.Erdos1041ClosePair.SegmentBound
