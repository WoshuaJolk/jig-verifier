import Mathlib

namespace Submissions.Erdos1041PureBinomial.ThroughCentre

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

/-- For `z ^ n - c` with `|c| < 1`, any two roots are joined through the
origin: on the ray from a root `a` to `0` the value is `c ((1 - t) ^ n - 1)`. -/
theorem proof :
    ∀ n : ℕ, 2 ≤ n → ∀ c : ℂ, ‖c‖ < 1 →
      (X ^ n - C c : ℂ[X]).natDegree = n ∧ (X ^ n - C c : ℂ[X]).Monic ∧
      (X ^ n - C c : ℂ[X]).rootSet ℂ ⊆ Metric.ball 0 1 ∧
        ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ (X ^ n - C c : ℂ[X]).roots ∧
          ∃ γ : Path z₁ z₂,
            Set.range γ ⊆ {z : ℂ | ‖(X ^ n - C c : ℂ[X]).eval z‖ < 1} ∧
              μH[1] (Set.range γ) < 2 := by
  intro n hn2 c hc
  obtain ⟨f, hfdef⟩ : ∃ f : ℂ[X], f = X ^ n - C c := ⟨_, rfl⟩
  rw [← hfdef]
  have hnat : f.natDegree = n := by
    rw [hfdef]
    exact natDegree_X_pow_sub_C
  have hmonic : f.Monic := by
    rw [hfdef]
    exact monic_X_pow_sub_C c (by omega)
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have heval : ∀ z : ℂ, f.eval z = z ^ n - c := by
    intro z
    rw [hfdef]
    simp
  have hrootpow : ∀ z ∈ f.roots, z ^ n = c := by
    intro z hz
    have h : f.eval z = 0 := (Polynomial.mem_roots hf0).mp hz
    rw [heval] at h
    exact sub_eq_zero.mp h
  have hrootnorm : ∀ z ∈ f.roots, ‖z‖ < 1 := by
    intro z hz
    by_contra hge
    have h1 : 1 ≤ ‖z‖ := not_lt.mp hge
    have h2 : (1 : ℝ) ≤ ‖z‖ ^ n := one_le_pow₀ h1
    have h3 : ‖z‖ ^ n = ‖c‖ := by rw [← norm_pow, hrootpow z hz]
    linarith
  have hcard : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hcardn : Multiset.card f.roots = n := by rw [hcard, hnat]
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
  have hbmem : b ∈ f.roots := by
    rw [hs1, hs2]
    simp
  have han := hrootpow a ha
  have hbn := hrootpow b hbmem
  have ha1 := hrootnorm a ha
  have hb1 := hrootnorm b hbmem
  have hlen : ‖a - 0‖ + ‖0 - b‖ < 2 := by
    rw [sub_zero, zero_sub, norm_neg]
    linarith
  have hbound : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖(((u ^ n - 1 : ℝ)) : ℂ) * c‖ < 1 := by
    intro u hu0 hu1
    have hp0 : 0 ≤ u ^ n := pow_nonneg hu0 n
    have hp1 : u ^ n ≤ 1 := pow_le_one₀ hu0 hu1
    have habs : |u ^ n - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |u ^ n - 1| * ‖c‖ ≤ 1 * ‖c‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg c)
      _ < 1 := by linarith
  have h1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (0 - a))‖ < 1 := by
    intro t ht0 ht1
    have e1 : a + (t : ℂ) * (0 - a) = ((1 - t : ℝ) : ℂ) * a := by
      push_cast
      ring
    have e2 : (((1 - t : ℝ) : ℂ) * a) ^ n - c = ((((1 - t) ^ n - 1 : ℝ)) : ℂ) * c := by
      rw [mul_pow, han]
      push_cast
      ring
    rw [heval, e1, e2]
    exact hbound (1 - t) (by linarith) (by linarith)
  have h2 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (0 + (t : ℂ) * (b - 0))‖ < 1 := by
    intro t ht0 ht1
    have e1 : 0 + (t : ℂ) * (b - 0) = (t : ℂ) * b := by ring
    have e2 : ((t : ℂ) * b) ^ n - c = (((t ^ n - 1 : ℝ)) : ℂ) * c := by
      rw [mul_pow, hbn]
      push_cast
      ring
    rw [heval, e1, e2]
    exact hbound t ht0 ht1
  have hsub : f.rootSet ℂ ⊆ Metric.ball 0 1 := by
    intro z hz
    have hz1 := (Polynomial.mem_rootSet_of_ne hf0).mp hz
    rw [Polynomial.coe_aeval_eq_eval] at hz1
    exact mem_ball_zero_iff.mpr (hrootnorm z ((Polynomial.mem_roots hf0).mpr hz1))
  obtain ⟨γ, hγ1, hγ2⟩ := two_leg f a 0 b hlen h1 h2
  exact ⟨hnat, hmonic, hsub, a, b, hab, γ, hγ1, hγ2⟩

end Submissions.Erdos1041PureBinomial.ThroughCentre
