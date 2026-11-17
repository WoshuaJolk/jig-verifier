import Mathlib

namespace Submissions.Erdos1041TwoLegCriterion.Polygonal

open Polynomial MeasureTheory ENNReal

/-- The straight path from `a` to `b`: its points are `a + t (b - a)` and its
length is at most the distance between the endpoints. -/
theorem seg_path (a b : ℂ) :
    ∃ γ : Path a b,
      (∀ z ∈ Set.range γ, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = a + (t : ℂ) * (b - a)) ∧
      μH[1] (Set.range γ) ≤ edist a b := by
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
  refine ⟨Path.ofLine hcont h0 h1, hmemimg, ?_⟩
  have hsub : Set.range (Path.ofLine hcont h0 h1) ⊆ segment ℝ a b := by
    intro z hz
    obtain ⟨t, ht0, ht1, rfl⟩ := hmemimg z hz
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  calc μH[1] (Set.range (Path.ofLine hcont h0 h1)) ≤ μH[1] (segment ℝ a b) := measure_mono hsub
    _ = edist a b := hausdorffMeasure_segment a b

/-- Two straight legs `a → w → b` inside the lemniscate, of total length below
two, give a path from `a` to `b` inside the lemniscate of length below two. -/
theorem two_leg (f : ℂ[X]) (a w b : ℂ) (hlen : ‖a - w‖ + ‖w - b‖ < 2)
    (h1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (w - a))‖ < 1)
    (h2 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (w + (t : ℂ) * (b - w))‖ < 1) :
    ∃ γ : Path a b, Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧ μH[1] (Set.range γ) < 2 := by
  obtain ⟨γ₁, hm1, hl1⟩ := seg_path a w
  obtain ⟨γ₂, hm2, hl2⟩ := seg_path w b
  refine ⟨γ₁.trans γ₂, ?_, ?_⟩
  · rw [Path.trans_range]
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨t, ht0, ht1, rfl⟩ := hm1 z hz
      exact h1 t ht0 ht1
    · obtain ⟨t, ht0, ht1, rfl⟩ := hm2 z hz
      exact h2 t ht0 ht1
  · rw [Path.trans_range]
    have hu : μH[1] (Set.range γ₁ ∪ Set.range γ₂)
        ≤ μH[1] (Set.range γ₁) + μH[1] (Set.range γ₂) := measure_union_le _ _
    have hd : dist a w + dist w b < 2 := by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlen
    have hsum : edist a w + edist w b < 2 := by
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
      calc ENNReal.ofReal (dist a w + dist w b) < ENNReal.ofReal 2 :=
            (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hd
        _ = 2 := by simp
    exact lt_of_le_of_lt (le_trans hu (add_le_add hl1 hl2)) hsum

theorem proof :
    ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∀ a b w : ℂ, ({a, b} : Multiset ℂ) ≤ f.roots →
      ‖a - w‖ + ‖w - b‖ < 2 →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (w - a))‖ < 1) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (w + (t : ℂ) * (b - w))‖ < 1) →
        ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
          ∃ γ : Path z₁ z₂,
            Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
              μH[1] (Set.range γ) < 2 := by
  intro n f _ _ _ _ a b w hab hlen h1 h2
  obtain ⟨γ, hγ1, hγ2⟩ := two_leg f a w b hlen h1 h2
  exact ⟨a, b, hab, γ, hγ1, hγ2⟩

end Submissions.Erdos1041TwoLegCriterion.Polygonal
