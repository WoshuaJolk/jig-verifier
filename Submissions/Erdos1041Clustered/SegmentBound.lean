import Mathlib

namespace Submissions.Erdos1041Clustered.SegmentBound

open Polynomial MeasureTheory ENNReal

/-- A product of factors `z - r`, each of modulus at most one. -/
theorem norm_prod_le_one (z : ℂ) (s : Multiset ℂ) (h : ∀ r ∈ s, ‖z - r‖ ≤ 1) :
    ‖(s.map (fun r => z - r)).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have h1 : ‖z - x‖ ≤ 1 := h x (Multiset.mem_cons_self x s)
    have h2 : ‖(s.map (fun r => z - r)).prod‖ ≤ 1 :=
      ih (fun r hr => h r (Multiset.mem_cons_of_mem hr))
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    calc ‖z - x‖ * ‖(s.map (fun r => z - r)).prod‖
        ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

/-- All roots in a closed disk of radius one half: any two roots are joined by
their segment, on which every factor has modulus at most one and the two near
factors contribute at most one quarter. -/
theorem proof :
    ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∀ c : ℂ, f.rootSet ℂ ⊆ Metric.closedBall c (1 / 2) →
        ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
          ∃ γ : Path z₁ z₂,
            Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
              μH[1] (Set.range γ) < 2 := by
  intro n f hn2 hdeg hmonic hroots c hclust
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hcard : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hcardn : Multiset.card f.roots = n := by rw [hcard, hdeg]
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card f.roots)
  obtain ⟨s1, hs1⟩ := Multiset.exists_cons_of_mem ha
  have hc1 : Multiset.card s1 = n - 1 := by
    have h := congrArg Multiset.card hs1
    rw [Multiset.card_cons, hcardn] at h
    omega
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card s1)
  obtain ⟨rest, hs2⟩ := Multiset.exists_cons_of_mem hb
  have hrest : f.roots = ({a, b} : Multiset ℂ) + rest := by
    rw [hs1, hs2, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
  have hab : ({a, b} : Multiset ℂ) ≤ f.roots := Multiset.le_iff_exists_add.mpr ⟨rest, hrest⟩
  have hinroot : ∀ r ∈ f.roots, r ∈ f.rootSet ℂ := by
    intro r hr
    refine (Polynomial.mem_rootSet_of_ne hf0).mpr ?_
    rw [Polynomial.coe_aeval_eq_eval]
    exact (Polynomial.mem_roots hf0).mp hr
  have hball : ∀ r ∈ f.roots, ‖r - c‖ ≤ 1 / 2 := by
    intro r hr
    have h := hclust (hinroot r hr)
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    exact h
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
  have hfac : (f.roots.map (fun r => X - C r)).prod = f :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
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
  have hac := hball a hamem
  have hbc := hball b hbmem
  have hd0 : 0 ≤ ‖b - a‖ := norm_nonneg _
  have hd1 : ‖b - a‖ ≤ 1 := by
    have e : b - a = (b - c) - (a - c) := by ring
    rw [e]
    have h := norm_sub_le (b - c) (a - c)
    linarith
  have hD1 : ‖b - a‖ * ‖b - a‖ ≤ 1 := by nlinarith
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (b - a))‖ < 1 := by
    intro t ht0 ht1
    have hzform : a + (t : ℂ) * (b - a) - c
        = ((1 - t : ℝ) : ℂ) * (a - c) + (t : ℂ) * (b - c) := by
      push_cast
      ring
    have hznorm : ‖a + (t : ℂ) * (b - a) - c‖ ≤ 1 / 2 := by
      rw [hzform]
      have h := norm_add_le (((1 - t : ℝ) : ℂ) * (a - c)) ((t : ℂ) * (b - c))
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), abs_of_nonneg ht0] at h
      have e1 : 0 ≤ (1 - t) * (1 / 2 - ‖a - c‖) := mul_nonneg (by linarith) (by linarith)
      have e2 : 0 ≤ t * (1 / 2 - ‖b - c‖) := mul_nonneg ht0 (by linarith)
      nlinarith [e1, e2]
    have hfactors : ∀ r ∈ rest, ‖a + (t : ℂ) * (b - a) - r‖ ≤ 1 := by
      intro r hr
      have hrmem : r ∈ f.roots := by
        rw [hrest]
        exact Multiset.mem_add.mpr (Or.inr hr)
      have e : a + (t : ℂ) * (b - a) - r = (a + (t : ℂ) * (b - a) - c) - (r - c) := by ring
      rw [e]
      have h := norm_sub_le (a + (t : ℂ) * (b - a) - c) (r - c)
      have h' := hball r hrmem
      linarith
    have hP := norm_prod_le_one (a + (t : ℂ) * (b - a)) rest hfactors
    have hprod : (a + (t : ℂ) * (b - a) - a) * (a + (t : ℂ) * (b - a) - b)
        = ((t * (t - 1) : ℝ) : ℂ) * ((b - a) * (b - a)) := by
      push_cast
      ring
    have hnonpos : t * (t - 1) ≤ 0 := by nlinarith
    have hq : -(t * (t - 1)) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hq0 : 0 ≤ -(t * (t - 1)) := by linarith
    rw [hev, hprod, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos hnonpos]
    have hstep1 : -(t * (t - 1)) * (‖b - a‖ * ‖b - a‖) ≤ 1 / 4 * 1 :=
      mul_le_mul hq hD1 (mul_nonneg hd0 hd0) (by norm_num)
    have hstep2 : -(t * (t - 1)) * (‖b - a‖ * ‖b - a‖)
          * ‖(rest.map (fun r => a + (t : ℂ) * (b - a) - r)).prod‖
        ≤ 1 / 4 * 1 * 1 :=
      mul_le_mul hstep1 hP (norm_nonneg _) (by norm_num)
    have hfin : (1 / 4 * 1 * 1 : ℝ) < 1 := by norm_num
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

end Submissions.Erdos1041Clustered.SegmentBound
