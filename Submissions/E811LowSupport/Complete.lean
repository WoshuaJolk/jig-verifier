import Mathlib

/- Component: LowSupportMass -/
open MeasureTheory
namespace LowSupportMass

lemma setIntegral_lt_mass {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (S : Set Ω) (f : Ω → ℝ)
    (hf : Integrable f (μ.restrict S)) (hS : 0 < μ S)
    (hbound : ∀ᵐ x ∂μ.restrict S, f x < 1) :
    (∫ x in S, f x ∂μ) < μ.real S := by
  have hpos : ∀ᵐ x ∂μ.restrict S, 0 < 1 - f x :=
    hbound.mono (fun _ hx => sub_pos.mpr hx)
  have hint : Integrable (fun x => (1 : ℝ) - f x) (μ.restrict S) :=
    (integrable_const 1).sub hf
  have hsupp : Function.support (fun x => (1 : ℝ) - f x) =ᵐ[μ.restrict S] Set.univ := by
    filter_upwards [hpos] with x hx
    apply propext
    change (1 - f x ≠ 0) ↔ True
    exact iff_true_intro (ne_of_gt hx)
  have hmeasure : (μ.restrict S) (Function.support (fun x => (1 : ℝ) - f x)) = μ S := by
    rw [measure_congr hsupp]
    simp
  have hi : 0 < ∫ x in S, (1 : ℝ) - f x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ hx => le_of_lt hx)) hint).mpr
    rw [hmeasure]
    exact hS
  rw [integral_sub (integrable_const 1) hf] at hi
  have hconst : (∫ _x in S, (1 : ℝ) ∂μ) = μ.real S := by simp [Measure.real]
  rw [hconst] at hi
  linarith


lemma at_most_two_heavy_classes {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, (1 : ℝ)/3 < p i) (hsum : ∑ i ∈ s, p i ≤ 1) :
    s.card ≤ 2 := by
  by_contra hc
  have hc3 : 3 ≤ s.card := by omega
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hne
  have hlt := Finset.sum_lt_sum (fun j hj => le_of_lt (hp j hj)) ⟨i,hi,hp i hi⟩
  have hconst : (∑ _j ∈ s, (1 : ℝ)/3) = (s.card : ℝ)/3 := by
    simp [div_eq_mul_inv]
  rw [hconst] at hlt
  have hcast : (3 : ℝ) ≤ s.card := by exact_mod_cast hc3
  linarith


lemma sum_fiber_mass_le_one {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → ι) (hT : Measurable T) (s : Finset ι) :
    (∑ i ∈ s, μ.real {x | T x = i}) ≤ 1 := by
  have he := sum_measureReal_preimage_singleton (μ := μ) s
    (fun i _ => hT (measurableSet_singleton i))
  change (∑ i ∈ s, μ.real (T ⁻¹' {i})) ≤ 1
  rw [he]
  have hb := measureReal_mono (μ := μ) (Set.subset_univ (T ⁻¹' (s : Set ι)))
  simpa using hb


lemma distinct_triples_inter_eq_pair {ι : Type*} [DecidableEq ι]
    (A B P : Finset ι) (hA : A.card = 3) (hB : B.card = 3)
    (hP : P.card = 2) (hne : A ≠ B) (hPA : P ⊆ A) (hPB : P ⊆ B) :
    A ∩ B = P := by
  have hsmall : (A ∩ B).card ≤ 2 := by
    by_contra h
    have ha : A ∩ B = A := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hb : A ∩ B = B := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    exact hne (ha.symm.trans hb)
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.subset_inter hPA hPB
  · omega

lemma missing_pair_on_distinct_types {ι : Type*} [DecidableEq ι]
    (A B P M : Finset ι) (hA : A.card = 3) (hB : B.card = 3)
    (hP : P.card = 2) (hM : M.card = 2) (hne : A ≠ B)
    (hPA : P ⊆ A) (hPB : P ⊆ B) (hMA : M ⊆ A) (hMB : M ⊆ B) :
    M = P := by
  have hi := distinct_triples_inter_eq_pair A B P hA hB hP hne hPA hPB
  apply Finset.eq_of_subset_of_card_le
  · rw [← hi]
    exact Finset.subset_inter hMA hMB
  · omega

lemma strict_partial_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (P : Finset ι)
    (hn : ∀ i, 0 ≤ w i) (ht : ∑ i, w i = 1)
    (hc : P.card < (Finset.univ.filter (fun i => 0 < w i)).card) :
    ∑ i ∈ P, w i < 1 := by
  classical
  have hex : ∃ i, 0 < w i ∧ i ∉ P := by
    by_contra h
    have hs : Finset.univ.filter (fun i => 0 < w i) ⊆ P := by
      intro i hi
      have hp := (Finset.mem_filter.mp hi).2
      by_contra hiP
      exact h ⟨i, hp, hiP⟩
    have := Finset.card_le_card hs
    omega
  obtain ⟨i, hi, hiP⟩ := hex
  have hle : ∑ j ∈ insert i P, w j ≤ ∑ j, w j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hn j)
  rw [Finset.sum_insert hiP, ht] at hle
  linarith

lemma class_mass_gt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (S : Set Ω) (f : Ω → ℝ) (δ : ℝ)
    (hf : Integrable f μ) (hS : 0 < μ S)
    (hzero : ∀ᵐ x ∂μ, x ∉ S → f x = 0)
    (hbound : ∀ᵐ x ∂μ.restrict S, f x < 1)
    (hrow : ∫ x, f x ∂μ = δ) : δ < μ.real S := by
  have he : (∫ x in S, f x ∂μ) = δ :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero hzero).trans hrow
  rw [← he]
  exact setIntegral_lt_mass S f hf.integrableOn hS hbound



end LowSupportMass

/- Component: LowSupportClassMass -/
open MeasureTheory
namespace LowSupportClassMass

lemma pair_row_class_mass {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : Set Ω) (W : Fin 6 → Ω → ℝ)
    (P : Finset (Fin 6)) (hP : P.card = 2) (hS : 0 < μ S)
    (hi : ∀ c, Integrable (W c) μ)
    (hr : ∀ c, ∫ y, W c y ∂μ = (1 : ℝ)/6)
    (hn : ∀ᵐ y ∂μ, ∀ c, 0 ≤ W c y)
    (ht : ∀ᵐ y ∂μ, ∑ c, W c y = 1)
    (hs : ∀ᵐ y ∂μ, 2 < (Finset.univ.filter (fun c => 0 < W c y)).card)
    (hz : ∀ᵐ y ∂μ, y ∉ S → ∀ c ∈ P, W c y = 0) :
    (1 : ℝ)/3 < μ.real S := by
  have hint : Integrable (fun y => ∑ c ∈ P, W c y) μ :=
    integrable_finsetSum P (fun c _ => hi c)
  have hrow : (∫ y, ∑ c ∈ P, W c y ∂μ) = (1 : ℝ)/3 := by
    rw [integral_finsetSum P (fun c _ => hi c)]
    simp_rw [hr]
    norm_num [hP]
  have hzero : ∀ᵐ y ∂μ, y ∉ S → (∑ c ∈ P, W c y) = 0 := by
    filter_upwards [hz] with y hy hyS
    exact Finset.sum_eq_zero (fun c hc => hy hyS c hc)
  have hb : ∀ᵐ y ∂μ, (∑ c ∈ P, W c y) < 1 := by
    filter_upwards [hn,ht,hs] with y hy ht hs
    exact LowSupportMass.strict_partial_sum (fun c => W c y) P hy ht (by omega)
  exact LowSupportMass.class_mass_gt S (fun y => ∑ c ∈ P, W c y) (1/3)
    hint hS hzero (ae_restrict_of_ae hb) hrow

end LowSupportClassMass

/- Component: LowSupportRows -/

open MeasureTheory

namespace LowSupportRows

variable {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]

noncomputable def activeLabels (μ : Measure Ω) (L : Ω × Ω → κ) (x : Ω) : Finset κ := by
  classical
  exact Finset.univ.filter (fun s => 0 < μ {y | L (x,y) = s})

@[simp] theorem mem_activeLabels (μ : Measure Ω) (L : Ω × Ω → κ) (x : Ω) (s : κ) :
    s ∈ activeLabels μ L x ↔ 0 < μ {y | L (x,y) = s} := by
  classical
  simp [activeLabels]

/-- Every finite-valued row takes an active value almost everywhere; no measurability needed. -/
theorem ae_row_active (μ : Measure Ω) (L : Ω × Ω → κ) (x : Ω) :
    ∀ᵐ y ∂μ, L (x,y) ∈ activeLabels μ L x := by
  classical
  have hs : ∀ s : κ, ∀ᵐ y ∂μ, L (x,y) = s → 0 < μ {z | L (x,z) = s} := by
    intro s
    by_cases h : μ {z | L (x,z) = s} = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with y hy
      exact fun he => False.elim (hy he)
    · exact Filter.Eventually.of_forall (fun _ _ => bot_lt_iff_ne_bot.mpr h)
  filter_upwards [ae_all_iff.mpr hs] with y hy
  exact (mem_activeLabels μ L x _).mpr (hy (L (x,y)) rfl)

variable [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Positive fiber mass is a measurable condition on the root. -/
theorem measurableSet_active_label (μ : Measure Ω) [SFinite μ]
    (L : Ω × Ω → κ) (hL : Measurable L) (s : κ) :
    MeasurableSet {x | s ∈ activeLabels μ L x} := by
  simp only [mem_activeLabels]
  have hm := measurable_measure_prodMk_left (ν := μ)
    (hL (measurableSet_singleton s))
  exact measurableSet_lt measurable_const hm

/-- Product-a.e. an edge label occurs on positive mass in its first endpoint's row. -/
theorem ae_prod_active (μ : Measure Ω) [SFinite μ]
    (L : Ω × Ω → κ) (hL : Measurable L) :
    ∀ᵐ p ∂(μ.prod μ), L p ∈ activeLabels μ L p.1 := by
  have hm : MeasurableSet {p : Ω × Ω | L p ∈ activeLabels μ L p.1} := by
    have he : {p : Ω × Ω | L p ∈ activeLabels μ L p.1} =
        ⋃ s : κ, {p | L p = s} ∩ {p | s ∈ activeLabels μ L p.1} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨L p,rfl,h⟩
      · rintro ⟨s,hs,h⟩; simpa [hs] using h
    rw [he]
    exact MeasurableSet.iUnion (fun s => (hL (measurableSet_singleton s)).inter
      ((measurableSet_active_label μ L hL s).preimage measurable_fst))
  exact (Measure.ae_prod_iff_ae_ae hm).mpr (Filter.Eventually.of_forall (ae_row_active μ L))

/-- Symmetry transfers row activity to both endpoints. -/
theorem ae_prod_active_both (μ : Measure Ω) [SFinite μ]
    (L : Ω × Ω → κ) (hL : Measurable L)
    (hsym : ∀ᵐ p ∂(μ.prod μ), L p = L (p.2,p.1)) :
    ∀ᵐ p ∂(μ.prod μ), L p ∈ activeLabels μ L p.1 ∧
      L p ∈ activeLabels μ L p.2 := by
  have hleft := ae_prod_active μ L hL
  have hright : ∀ᵐ p ∂(μ.prod μ), L (p.2,p.1) ∈ activeLabels μ L p.2 := by
    exact (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hleft
  filter_upwards [hleft,hright,hsym] with p hl hr hs
  exact ⟨hl, by rw [hs]; exact hr⟩

section ColorSupport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def colorSupport (W : ι → Ω × Ω → ℝ) (p : Ω × Ω) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < W i p)

noncomputable def missingColors (W : ι → Ω × Ω → ℝ) (p : Ω × Ω) : Finset ι :=
  (colorSupport W p)ᶜ

@[simp] theorem mem_colorSupport (W : ι → Ω × Ω → ℝ) (p : Ω × Ω) (i : ι) :
    i ∈ colorSupport W p ↔ 0 < W i p := by
  classical
  simp [colorSupport]

@[simp] theorem mem_missingColors (W : ι → Ω × Ω → ℝ) (p : Ω × Ω) (i : ι) :
    i ∈ missingColors W p ↔ W i p ≤ 0 := by
  simp [missingColors]

/-- The finite positive-support map is measurable. -/
theorem measurable_colorSupport (W : ι → Ω × Ω → ℝ) (hW : ∀ i, Measurable (W i)) :
    Measurable (colorSupport W) := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [mem_colorSupport]
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hW i))

/-- The finite missing-color map is measurable. -/
theorem measurable_missingColors (W : ι → Ω × Ω → ℝ) (hW : ∀ i, Measurable (W i)) :
    Measurable (missingColors W) := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [mem_missingColors]
  exact measurableSet_setOfPred.mp (measurableSet_le (hW i) measurable_const)

theorem ae_colorSupport_symm (μ : Measure Ω) (W : ι → Ω × Ω → ℝ)
    (hs : ∀ i, ∀ᵐ p ∂(μ.prod μ), W i p = W i (p.2,p.1)) :
    ∀ᵐ p ∂(μ.prod μ), colorSupport W p = colorSupport W (p.2,p.1) := by
  filter_upwards [ae_all_iff.mpr hs] with p hp
  ext i
  simp only [mem_colorSupport, hp i]

theorem ae_missingColors_symm (μ : Measure Ω) (W : ι → Ω × Ω → ℝ)
    (hs : ∀ i, ∀ᵐ p ∂(μ.prod μ), W i p = W i (p.2,p.1)) :
    ∀ᵐ p ∂(μ.prod μ), missingColors W p = missingColors W (p.2,p.1) := by
  filter_upwards [ae_colorSupport_symm μ W hs] with p hp
  simp only [missingColors, hp]

/-- Almost every actual support label is active at both endpoints. -/
theorem ae_support_active_both (μ : Measure Ω) [SFinite μ]
    (W : ι → Ω × Ω → ℝ) (hW : ∀ i, Measurable (W i))
    (hs : ∀ i, ∀ᵐ p ∂(μ.prod μ), W i p = W i (p.2,p.1)) :
    ∀ᵐ p ∂(μ.prod μ),
      colorSupport W p ∈ activeLabels μ (colorSupport W) p.1 ∧
      colorSupport W p ∈ activeLabels μ (colorSupport W) p.2 :=
  ae_prod_active_both μ (colorSupport W) (measurable_colorSupport W hW)
    (ae_colorSupport_symm μ W hs)

/-- Almost every actual missing label is active at both endpoints. -/
theorem ae_missing_active_both (μ : Measure Ω) [SFinite μ]
    (W : ι → Ω × Ω → ℝ) (hW : ∀ i, Measurable (W i))
    (hs : ∀ i, ∀ᵐ p ∂(μ.prod μ), W i p = W i (p.2,p.1)) :
    ∀ᵐ p ∂(μ.prod μ),
      missingColors W p ∈ activeLabels μ (missingColors W) p.1 ∧
      missingColors W p ∈ activeLabels μ (missingColors W) p.2 :=
  ae_prod_active_both μ (missingColors W) (measurable_missingColors W hW)
    (ae_missingColors_symm μ W hs)

end ColorSupport

/-- An almost-everywhere relation holds between any two positive-mass fibers. -/
theorem relation_of_positive_fibers {α β : Type*} (μ : Measure Ω)
    (f : Ω → α) (g : Ω → β) (R : α → β → Prop) (a : α) (b : β)
    (ha : 0 < μ {y | f y = a}) (hb : 0 < μ {z | g z = b})
    (hR : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, R (f y) (g z)) : R a b := by
  have hf : ∃ y, f y = a ∧ ∀ᵐ z ∂μ, R (f y) (g z) :=
    ((frequently_ae_iff.mpr (ne_of_gt ha)).and_eventually hR).exists
  obtain ⟨y,hy,hyR⟩ := hf
  have hg : ∃ z, g z = b ∧ R (f y) (g z) :=
    ((frequently_ae_iff.mpr (ne_of_gt hb)).and_eventually hyR).exists
  obtain ⟨z,hz,h⟩ := hg
  simpa [hy,hz] using h

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- A row relation transfers to every pair of active finite labels. -/
theorem relation_on_activeLabels (μ : Measure Ω) (L : Ω × Ω → κ)
    (x : Ω) (R : κ → κ → Prop)
    (hR : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, R (L (x,y)) (L (x,z))) :
    ∀ a ∈ activeLabels μ L x, ∀ b ∈ activeLabels μ L x, R a b := by
  intro a ha b hb
  exact relation_of_positive_fibers μ (fun y => L (x,y)) (fun z => L (x,z)) R a b
    ((mem_activeLabels μ L x a).mp ha) ((mem_activeLabels μ L x b).mp hb) hR

end LowSupportRows




/- Component: LowSupportTypeFamily -/

open MeasureTheory

namespace LowSupportTypeFamily
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def activeTypes (μ : Measure Ω) (T : Ω → Finset (Fin 6)) : Finset (Finset (Fin 6)) := by
  classical
  exact Finset.univ.filter (fun S => 0 < μ {x | T x = S})

@[simp] theorem mem_activeTypes (μ : Measure Ω) (T : Ω → Finset (Fin 6)) (S : Finset (Fin 6)) :
    S ∈ activeTypes μ T ↔ 0 < μ {x | T x = S} := by
  classical
  simp [activeTypes]

theorem ae_type_active (μ : Measure Ω) (T : Ω → Finset (Fin 6)) :
    ∀ᵐ x ∂μ, T x ∈ activeTypes μ T := by
  have hs : ∀ S : Finset (Fin 6), ∀ᵐ x ∂μ, T x = S → 0 < μ {y | T y = S} := by
    intro S
    by_cases h : μ {y | T y = S} = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with x hx
      exact fun he => False.elim (hx he)
    · exact Filter.Eventually.of_forall (fun _ _ => bot_lt_iff_ne_bot.mpr h)
  filter_upwards [ae_all_iff.mpr hs] with x hx
  exact (mem_activeTypes μ T _).mpr (hx (T x) rfl)

theorem activeTypes_card_three (μ : Measure Ω) (T : Ω → Finset (Fin 6))
    (hc : ∀ᵐ x ∂μ, (T x).card = 3) :
    ∀ S ∈ activeTypes μ T, S.card = 3 := by
  intro S hS
  have hp := (mem_activeTypes μ T S).mp hS
  obtain ⟨x,hx,hxc⟩ := ((frequently_ae_iff.mpr (ne_of_gt hp)).and_eventually hc).exists
  simpa [hx] using hxc

/-- Positive-measure type classes inherit the pairwise intersection bound. -/
theorem activeTypes_inter_card (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6)) (T : Ω → Finset (Fin 6))
    (hc : ∀ᵐ p ∂(μ.prod μ), (M p).card = 2)
    (hsub : ∀ᵐ p ∂(μ.prod μ), M p ⊆ T p.1 ∩ T p.2) :
    ∀ S ∈ activeTypes μ T, ∀ U ∈ activeTypes μ T, 2 ≤ (S ∩ U).card := by
  have hi : ∀ᵐ p ∂(μ.prod μ), 2 ≤ (T p.1 ∩ T p.2).card := by
    filter_upwards [hc,hsub] with p hp hs
    have h := Finset.card_le_card hs
    simpa [hp] using h
  intro S hS U hU
  exact LowSupportRows.relation_of_positive_fibers μ T T
    (fun S U => 2 ≤ (S ∩ U).card) S U
    ((mem_activeTypes μ T S).mp hS) ((mem_activeTypes μ T U).mp hU)
    (Measure.ae_ae_of_ae_prod hi)

/-- A color outside every active type is absent from the missing map almost everywhere. -/
theorem ae_not_mem_missing_of_type_container (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6)) (T : Ω → Finset (Fin 6))
    (hsub : ∀ᵐ p ∂(μ.prod μ), M p ⊆ T p.1 ∩ T p.2)
    (U : Finset (Fin 6)) (hU : ∀ S ∈ activeTypes μ T, S ⊆ U)
    (c : Fin 6) (hc : c ∉ U) : ∀ᵐ p ∂(μ.prod μ), c ∉ M p := by
  have ha : ∀ᵐ p ∂(μ.prod μ), T p.1 ∈ activeTypes μ T :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (ae_type_active μ T)
  filter_upwards [ha,hsub] with p hp hs
  intro hm
  exact hc (hU (T p.1) hp (Finset.mem_inter.mp (hs hm)).1)

/-- For the concrete missing-color map, the outside color is universally positive. -/
theorem ae_positive_of_type_container (μ : Measure Ω) [SFinite μ]
    (W : Fin 6 → Ω × Ω → ℝ) (T : Ω → Finset (Fin 6))
    (hsub : ∀ᵐ p ∂(μ.prod μ), LowSupportRows.missingColors W p ⊆ T p.1 ∩ T p.2)
    (U : Finset (Fin 6)) (hU : ∀ S ∈ activeTypes μ T, S ⊆ U)
    (c : Fin 6) (hc : c ∉ U) : ∀ᵐ p ∂(μ.prod μ), 0 < W c p := by
  filter_upwards [ae_not_mem_missing_of_type_container μ (LowSupportRows.missingColors W) T hsub U hU c hc] with p hp
  simpa only [LowSupportRows.mem_missingColors,not_le] using hp

end LowSupportTypeFamily


/- Component: LowSupportClassBlocks -/
open MeasureTheory
namespace LowSupportClassBlocks

lemma pair_zero_between_types {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Fin 6 → Ω × Ω → ℝ)
    (T : Ω → Finset (Fin 6)) (P : Finset (Fin 6)) (hP : P.card = 2)
    (hc : ∀ᵐ x ∂μ, (T x).card = 3)
    (hm : ∀ᵐ p ∂μ.prod μ, (LowSupportRows.missingColors W p).card = 2)
    (hsub : ∀ᵐ p ∂μ.prod μ, LowSupportRows.missingColors W p ⊆ T p.1 ∩ T p.2)
    (hp : ∀ S ∈ LowSupportTypeFamily.activeTypes μ T, P ⊆ S)
    (hn : ∀ᵐ p ∂μ.prod μ, ∀ c, 0 ≤ W c p) :
    ∀ᵐ p ∂μ.prod μ, T p.1 ≠ T p.2 → ∀ c ∈ P, W c p = 0 := by
  have ha := LowSupportTypeFamily.ae_type_active μ T
  have hleft := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hc.and ha)
  have hright := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hc.and ha)
  filter_upwards [hleft,hright,hm,hsub,hn] with p hl hr hm hs hn hne c hcP
  have he := LowSupportMass.missing_pair_on_distinct_types (T p.1) (T p.2) P
    (LowSupportRows.missingColors W p) hl.1 hr.1 hP hm hne
    (hp _ hl.2) (hp _ hr.2)
    (fun i hi => (Finset.mem_inter.mp (hs hi)).1)
    (fun i hi => (Finset.mem_inter.mp (hs hi)).2)
  have hmem : c ∈ LowSupportRows.missingColors W p := by rw [he]; exact hcP
  exact le_antisymm ((LowSupportRows.mem_missingColors W p c).mp hmem) (hn c)

end LowSupportClassBlocks

/- Component: LowSupportHeavyClasses -/

open MeasureTheory
namespace LowSupportHeavyClasses

/-- Every active class is heavier than one third when a shared color pair vanishes
between distinct classes. This selects a good row from each positive-measure class. -/
theorem active_class_mass_gt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ = (1 : ℝ)/6)
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (hs : ∀ᵐ p ∂μ.prod μ, 2 < (Finset.univ.filter (fun c => 0 < W c p)).card)
    (T : Ω → Finset (Fin 6)) (P : Finset (Fin 6)) (hP : P.card = 2)
    (hz : ∀ᵐ p ∂μ.prod μ, T p.1 ≠ T p.2 → ∀ c ∈ P, W c p = 0) :
    ∀ S ∈ LowSupportTypeFamily.activeTypes μ T, (1 : ℝ)/3 < μ.real {x | T x = S} := by
  have hball : ∀ᵐ x ∂μ, ∀ c, ∀ᵐ y ∂μ, 0 ≤ W c (x,y) ∧ W c (x,y) ≤ 1 :=
    ae_all_iff.mpr (fun c => Measure.ae_ae_of_ae_prod (hb c))
  have hrall : ∀ᵐ x ∂μ, ∀ c, ∫ y, W c (x,y) ∂μ = (1 : ℝ)/6 := ae_all_iff.mpr hr
  have hgood := hball.and (hrall.and ((Measure.ae_ae_of_ae_prod ht).and
    ((Measure.ae_ae_of_ae_prod hs).and (Measure.ae_ae_of_ae_prod hz))))
  intro S hS
  have hp := (LowSupportTypeFamily.mem_activeTypes μ T S).mp hS
  obtain ⟨x, hxS, hxb, hxr, hxt, hxs, hxz⟩ :=
    ((frequently_ae_iff.mpr (ne_of_gt hp)).and_eventually hgood).exists
  apply LowSupportClassMass.pair_row_class_mass {y | T y = S}
    (fun c y => W c (x,y)) P hP hp
  · intro c
    apply (integrable_const (1 : ℝ)).mono'
      ((hW c).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    filter_upwards [hxb c] with y hy
    change ‖W c (x,y)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hy.1]
    exact hy.2
  · exact hxr
  · filter_upwards [ae_all_iff.mpr hxb] with y hy
    exact fun c => (hy c).1
  · exact hxt
  · exact hxs
  · filter_upwards [hxz] with y hy hnot
    apply hy
    intro he
    apply hnot
    exact he.symm.trans hxS


/-- The common-pair hypotheses on the missing-color types imply the required
strict lower bound for every active type class. -/
theorem active_class_mass_gt_of_common_pair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ = (1 : ℝ)/6)
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (hs : ∀ᵐ p ∂μ.prod μ, 2 < (Finset.univ.filter (fun c => 0 < W c p)).card)
    (T : Ω → Finset (Fin 6)) (P : Finset (Fin 6)) (hP : P.card = 2)
    (hc : ∀ᵐ x ∂μ, (T x).card = 3)
    (hm : ∀ᵐ p ∂μ.prod μ, (LowSupportRows.missingColors W p).card = 2)
    (hsub : ∀ᵐ p ∂μ.prod μ, LowSupportRows.missingColors W p ⊆ T p.1 ∩ T p.2)
    (hp : ∀ S ∈ LowSupportTypeFamily.activeTypes μ T, P ⊆ S) :
    ∀ S ∈ LowSupportTypeFamily.activeTypes μ T, (1 : ℝ)/3 < μ.real {x | T x = S} := by
  apply active_class_mass_gt μ W hW hb hr ht hs T P hP
  apply LowSupportClassBlocks.pair_zero_between_types W T P hP hc hm hsub hp
  filter_upwards [ae_all_iff.mpr hb] with p hbp
  exact fun c => (hbp c).1

end LowSupportHeavyClasses



/- Component: LowSupportCombinatorics -/

namespace LowSupportCombinatorics

/-- A two-element set meeting the three sides of a triangle lies in that triangle. -/
theorem pair_meeting_triangle {α : Type*} [DecidableEq α]
    (a b c : α) (hneab : a ≠ b) (hneac : a ≠ c) (hnebc : b ≠ c) (P : Finset α) (hP : P.card = 2)
    (hab : a ∈ P ∨ b ∈ P) (hac : a ∈ P ∨ c ∈ P)
    (hbc : b ∈ P ∨ c ∈ P) : P ⊆ {a, b, c} := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hab hac hbc
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl
  · aesop
  · aesop

/-- Any pair meeting all three sides of a triangle is one of those sides. -/
theorem pair_eq_triangle_side {α : Type*} [DecidableEq α]
    (a b c : α) (hneab : a ≠ b) (hneac : a ≠ c) (hnebc : b ≠ c) (P : Finset α) (hP : P.card = 2)
    (hab : a ∈ P ∨ b ∈ P) (hac : a ∈ P ∨ c ∈ P)
    (hbc : b ∈ P ∨ c ∈ P) :
    P = {a,b} ∨ P = {a,c} ∨ P = {b,c} := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hab hac hbc
  aesop (add simp [Finset.pair_comm])

theorem intersecting_pair_family (F : Finset (Finset (Fin 6)))
    (hcard : ∀ P ∈ F, P.card = 2)
    (hmeet : ∀ P ∈ F, ∀ Q ∈ F, ∃ x, x ∈ P ∧ x ∈ Q)
    (hno : ∀ a : Fin 6, ∃ P ∈ F, a ∉ P) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ P ∈ F, P = {a,b} ∨ P = {a,c} ∨ P = {b,c} := by
  obtain ⟨A, hAF, _⟩ := hno 0
  obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp (hcard A hAF)
  subst A
  obtain ⟨B, hBF, haB⟩ := hno a
  have hbB : b ∈ B := by
    obtain ⟨x, hx, hxB⟩ := hmeet {a,b} hAF B hBF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact False.elim (haB hxB)
    · exact hxB
  obtain ⟨c, hbc, hB⟩ : ∃ c, b ≠ c ∧ B = {b,c} := by
    obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (hcard B hBF)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbB
    rcases hbB with rfl | rfl
    · exact ⟨v, huv, rfl⟩
    · exact ⟨u, Ne.symm huv, Finset.pair_comm u b⟩
  subst B
  have hac : a ≠ c := by
    intro h
    exact haB (by simp [h])
  obtain ⟨C, hCF, hbC⟩ := hno b
  have haC : a ∈ C := by
    obtain ⟨x,hx,hxC⟩ := hmeet {a,b} hAF C hCF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hxC
    · exact False.elim (hbC hxC)
  have hcC : c ∈ C := by
    obtain ⟨x,hx,hxC⟩ := hmeet {b,c} hBF C hCF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact False.elim (hbC hxC)
    · exact hxC
  have hC : C = {a,c} := by
    obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (hcard C hCF)
    simp only [Finset.mem_insert, Finset.mem_singleton] at haC hcC
    aesop (add simp [Finset.pair_comm])
  subst C
  refine ⟨a,b,c,hab,hac,hbc,?_⟩
  intro P hPF
  have meet (u v : Fin 6) (h : {u,v} ∈ F) : u ∈ P ∨ v ∈ P := by
    obtain ⟨x,hx,hxP⟩ := hmeet {u,v} h P hPF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hxP
    · exact Or.inr hxP
  exact pair_eq_triangle_side a b c hab hac hbc P (hcard P hPF)
    (meet a b hAF) (meet a c hCF) (meet b c hBF)

/-- Two points of a three-point set must be present if the third is absent. -/
theorem inter_triple_forces_pair {α : Type*} [DecidableEq α]
    (P : Finset α) (a b c : α) (ha : a ∉ P)
    (h : 2 ≤ (P ∩ {a,b,c}).card) : b ∈ P ∧ c ∈ P := by
  constructor
  · by_contra hb
    have hs : P ∩ {a,b,c} ⊆ {c} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      aesop
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    omega
  · by_contra hc
    have hs : P ∩ {a,b,c} ⊆ {b} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      aesop
    have hb := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hb
    omega

/-- The key local step in the common-pair-or-four-container classification. -/
theorem triple_meeting_two_triples {α : Type*} [DecidableEq α]
    (P : Finset α) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcard : P.card = 3)
    (h₁ : 2 ≤ (P ∩ {a,b,c}).card)
    (h₂ : 2 ≤ (P ∩ {a,b,d}).card) :
    {a,b} ⊆ P ∨ P ⊆ {a,b,c,d} := by
  by_cases ha : a ∈ P
  · by_cases hb : b ∈ P
    · exact Or.inl (by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; aesop)
    · have h₁' : 2 ≤ (P ∩ {b,a,c}).card := by
        simpa [Finset.insert_comm] using h₁
      have h₂' : 2 ≤ (P ∩ {b,a,d}).card := by
        simpa [Finset.insert_comm] using h₂
      have hc := (inter_triple_forces_pair P b a c hb h₁').2
      have hd := (inter_triple_forces_pair P b a d hb h₂').2
      have hs : {a,c,d} ⊆ P := by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; aesop
      have he : {a,c,d} = P := Finset.eq_of_subset_of_card_le hs (by simp [hcard,hac,had,hcd])
      subst P
      exact Or.inr (by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; aesop)
  · have hb := (inter_triple_forces_pair P a b c ha h₁).1
    have hc := (inter_triple_forces_pair P a b c ha h₁).2
    have hd := (inter_triple_forces_pair P a b d ha h₂).2
    have hs : {b,c,d} ⊆ P := by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; aesop
    have he : {b,c,d} = P := Finset.eq_of_subset_of_card_le hs (by simp [hcard,hbc,hbd,hcd])
    subst P
    exact Or.inr (by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; aesop)

/-- A third type outside the common-pair star forces the four-element container. -/
theorem triple_forced_container {α : Type*} [DecidableEq α]
    (P : Finset α) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hp : P.card = 3)
    (h₁ : 2 ≤ (P ∩ {a,b,c}).card)
    (h₂ : 2 ≤ (P ∩ {a,b,d}).card)
    (h₃ : 2 ≤ (P ∩ {a,c,d}).card) : P ⊆ {a,b,c,d} := by
  rcases triple_meeting_two_triples P a b c d hab hac had hbc hbd hcd hp h₁ h₂ with hs | hs
  · have ha : a ∈ P := hs (by simp)
    have hb : b ∈ P := hs (by simp)
    have hcdP : c ∈ P ∨ d ∈ P := by
      by_contra! hn
      have hz : P ∩ {a,c,d} ⊆ {a} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        aesop
      have hh := Finset.card_le_card hz
      simp only [Finset.card_singleton] at hh
      omega
    rcases hcdP with hc | hd
    · have hz : {a,b,c} ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        aesop
      have he : {a,b,c} = P := Finset.eq_of_subset_of_card_le hz (by simp [hp,hab,hac,hbc])
      subst P
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
      aesop
    · have hz : {a,b,d} ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        aesop
      have he : {a,b,d} = P := Finset.eq_of_subset_of_card_le hz (by simp [hp,hab,had,hbd])
      subst P
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
      aesop
  · exact hs

/-- Normal-form version of the whole triple-family dichotomy. -/
theorem triple_family_normal_form {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcard : ∀ P ∈ F, P.card = 3)
    (hmeet : ∀ P ∈ F, ∀ Q ∈ F, 2 ≤ (P ∩ Q).card)
    (hA : {a,b,c} ∈ F) (hB : {a,b,d} ∈ F) :
    (∀ P ∈ F, {a,b} ⊆ P) ∨ (∀ P ∈ F, P ⊆ {a,b,c,d}) := by
  by_cases hstar : ∀ P ∈ F, {a,b} ⊆ P
  · exact Or.inl hstar
  push Not at hstar
  obtain ⟨Q,hQ,hnot⟩ := hstar
  have hqa : a ∉ Q ∨ b ∉ Q := by
    by_contra! hh
    apply hnot
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    aesop
  have hQform : Q = {a,c,d} ∨ Q = {b,c,d} := by
    rcases hqa with ha | hb
    · have h₁ := inter_triple_forces_pair Q a b c ha (hmeet Q hQ _ hA)
      have h₂ := inter_triple_forces_pair Q a b d ha (hmeet Q hQ _ hB)
      have hz : {b,c,d} ⊆ Q := by
        intro x hx
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        aesop
      exact Or.inr (Finset.eq_of_subset_of_card_le hz (by simp [hcard Q hQ,hbc,hbd,hcd])).symm
    · have hi₁ : 2 ≤ (Q ∩ {b,a,c}).card := by simpa [Finset.insert_comm] using hmeet Q hQ _ hA
      have hi₂ : 2 ≤ (Q ∩ {b,a,d}).card := by simpa [Finset.insert_comm] using hmeet Q hQ _ hB
      have h₁ := inter_triple_forces_pair Q b a c hb hi₁
      have h₂ := inter_triple_forces_pair Q b a d hb hi₂
      have hz : {a,c,d} ⊆ Q := by
        intro x hx
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        aesop
      exact Or.inl (Finset.eq_of_subset_of_card_le hz (by simp [hcard Q hQ,hac,had,hcd])).symm
  right
  intro P hP
  rcases hQform with hQeq | hQeq
  · subst Q
    exact triple_forced_container P a b c d hab hac had hbc hbd hcd (hcard P hP)
      (hmeet P hP _ hA) (hmeet P hP _ hB) (hmeet P hP _ hQ)
  · subst Q
    have h₁ : 2 ≤ (P ∩ {b,a,c}).card := by simpa [Finset.insert_comm] using hmeet P hP _ hA
    have h₂ : 2 ≤ (P ∩ {b,a,d}).card := by simpa [Finset.insert_comm] using hmeet P hP _ hB
    have h := triple_forced_container P b a c d (Ne.symm hab) hbc hbd hac had hcd
      (hcard P hP) h₁ h₂ (hmeet P hP _ hQ)
    simpa [Finset.insert_comm] using h

/-- Full finite triple-family common-pair/four-container classification. -/
theorem triple_family_classification (F : Finset (Finset (Fin 6)))
    (hcard : ∀ P ∈ F, P.card = 3)
    (hmeet : ∀ P ∈ F, ∀ Q ∈ F, 2 ≤ (P ∩ Q).card) :
    (∃ C : Finset (Fin 6), C.card = 2 ∧ ∀ P ∈ F, C ⊆ P) ∨
    (∃ U : Finset (Fin 6), U.card ≤ 4 ∧ ∀ P ∈ F, P ⊆ U) := by
  by_cases hn : F.Nonempty
  · obtain ⟨A,hA⟩ := hn
    by_cases hall : ∀ B ∈ F, B = A
    · exact Or.inr ⟨A, by have h := hcard A hA; omega, by intro B hB; rw [hall B hB]⟩
    push Not at hall
    obtain ⟨B,hB,hBA⟩ := hall
    have hi : (A ∩ B).card = 2 := by
      have hlo := hmeet A hA B hB
      have hhi := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
      have hca := hcard A hA
      have hcb := hcard B hB
      have hn3 : (A ∩ B).card ≠ 3 := by
        intro he
        have heA : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        have hs : A ⊆ B := by rw [← heA]; exact Finset.inter_subset_right
        exact hBA (Finset.eq_of_subset_of_card_le hs (by omega)).symm
      omega
    obtain ⟨a,b,hab,hiab⟩ := Finset.card_eq_two.mp hi
    have hsubA : {a,b} ⊆ A := by rw [← hiab]; exact Finset.inter_subset_left
    have hsubB : {a,b} ⊆ B := by rw [← hiab]; exact Finset.inter_subset_right
    have hcA : (A \ {a,b}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsubA, hcard A hA]
      simp [hab]
    have hcB : (B \ {a,b}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsubB, hcard B hB]
      simp [hab]
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hcA
    obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hcB
    have hcA' : c ∈ A ∧ c ∉ ({a,b} : Finset (Fin 6)) := by
      apply Finset.mem_sdiff.mp
      rw [hc]
      simp
    have hdB' : d ∈ B ∧ d ∉ ({a,b} : Finset (Fin 6)) := by
      apply Finset.mem_sdiff.mp
      rw [hd]
      simp
    have hac : a ≠ c := by aesop
    have hbc : b ≠ c := by aesop
    have had : a ≠ d := by aesop
    have hbd : b ≠ d := by aesop
    have hAe : A = {a,b,c} := by
      have h := Finset.union_sdiff_of_subset hsubA
      rw [hc] at h
      simpa using h.symm
    have hBe : B = {a,b,d} := by
      have h := Finset.union_sdiff_of_subset hsubB
      rw [hd] at h
      simpa using h.symm
    have hcd : c ≠ d := by intro he; apply hBA; rw [hAe,hBe,he]
    subst A
    subst B
    rcases triple_family_normal_form F a b c d hab hac had hbc hbd hcd hcard hmeet hA hB with hs | ht
    · exact Or.inl ⟨{a,b}, by simp [hab], hs⟩
    · exact Or.inr ⟨{a,b,c,d}, by simp [hab,hac,had,hbc,hbd,hcd], ht⟩
  · right
    refine ⟨∅, by simp, ?_⟩
    intro P hP
    exact False.elim (hn ⟨P,hP⟩)

end LowSupportCombinatorics



/- Component: LowSupportTypeClosure -/

namespace LowSupportTypeClosure

/-- Three classes each heavier than one third exceed total mass one. -/
theorem at_most_two_heavy {α : Type*} [DecidableEq α]
    (F : Finset α) (p : α → ℝ)
    (hsum : ∑ a ∈ F, p a ≤ 1)
    (hheavy : ∀ a ∈ F, (1 : ℝ)/3 < p a) : F.card ≤ 2 := by
  by_contra! hc
  have hn : F.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : ∑ a ∈ F, (1 : ℝ)/3 < ∑ a ∈ F, p a :=
    Finset.sum_lt_sum_of_nonempty hn hheavy
  simp only [Finset.sum_const, nsmul_eq_mul] at hstrict
  have hcast : (3 : ℝ) ≤ F.card := by exact_mod_cast hc
  nlinarith

/-- A family of at most two triples sharing a pair uses at most four colors. -/
theorem union_small_of_common_pair (F : Finset (Finset (Fin 6)))
    (hcard : ∀ A ∈ F, A.card = 3)
    (P : Finset (Fin 6)) (hP : P.card = 2)
    (hsub : ∀ A ∈ F, P ⊆ A) (hsmall : F.card ≤ 2) :
    (F.biUnion id).card ≤ 4 := by
  have hs : F.biUnion id ⊆ P ∪ F.biUnion (fun A => A \ P) := by
    intro x hx
    obtain ⟨A,hA,hxA⟩ := Finset.mem_biUnion.mp hx
    by_cases hp : x ∈ P
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_sdiff.mpr ⟨hxA,hp⟩⟩)
  have hd : ∀ A ∈ F, (A \ P).card = 1 := by
    intro A hA
    rw [Finset.card_sdiff_of_subset (hsub A hA), hcard A hA, hP]
  calc
    (F.biUnion id).card ≤ (P ∪ F.biUnion (fun A => A \ P)).card := Finset.card_le_card hs
    _ ≤ P.card + (F.biUnion (fun A => A \ P)).card := Finset.card_union_le _ _
    _ ≤ 2 + ∑ A ∈ F, (A \ P).card := by
      rw [hP]
      exact Nat.add_le_add_left (Finset.card_biUnion_le) 2
    _ = 2 + F.card := by
      have he : (∑ A ∈ F, (A \ P).card) = ∑ _A ∈ F, 1 := Finset.sum_congr rfl hd
      rw [he]
      simp
    _ ≤ 4 := by omega

/-- Common-pair branch plus heavy class masses gives a four-color union. -/
theorem union_small_of_heavy_common_pair (F : Finset (Finset (Fin 6)))
    (p : Finset (Fin 6) → ℝ)
    (hcard : ∀ A ∈ F, A.card = 3)
    (hsum : ∑ A ∈ F, p A ≤ 1)
    (P : Finset (Fin 6)) (hP : P.card = 2)
    (hsub : ∀ A ∈ F, P ⊆ A)
    (hheavy : ∀ A ∈ F, (1 : ℝ)/3 < p A) :
    (F.biUnion id).card ≤ 4 :=
  union_small_of_common_pair F hcard P hP hsub (at_most_two_heavy F p hsum hheavy)

/-- The finite closing step, with the already-proved classification supplied explicitly. -/
theorem union_small_from_classification (F : Finset (Finset (Fin 6)))
    (p : Finset (Fin 6) → ℝ)
    (hcard : ∀ A ∈ F, A.card = 3)
    (hsum : ∑ A ∈ F, p A ≤ 1)
    (hclass : (∃ P : Finset (Fin 6), P.card = 2 ∧ ∀ A ∈ F, P ⊆ A) ∨
      (∃ U : Finset (Fin 6), U.card ≤ 4 ∧ ∀ A ∈ F, A ⊆ U))
    (hheavy : ∀ P : Finset (Fin 6), P.card = 2 → (∀ A ∈ F, P ⊆ A) →
      3 ≤ F.card → ∀ A ∈ F, (1 : ℝ)/3 < p A) :
    (F.biUnion id).card ≤ 4 := by
  rcases hclass with ⟨P,hP,hsub⟩ | ⟨U,hU,hsub⟩
  · by_cases hs : F.card ≤ 2
    · exact union_small_of_common_pair F hcard P hP hsub hs
    · exact union_small_of_heavy_common_pair F p hcard hsum P hP hsub
        (hheavy P hP hsub (by omega))
  · apply (Finset.card_le_card ?_).trans hU
    intro x hx
    obtain ⟨A,hA,hxA⟩ := Finset.mem_biUnion.mp hx
    exact hsub A hA hxA

/-- Full finite type-and-mass closing lemma, invoking the proved triple classification. -/
theorem type_union_card_le_four (F : Finset (Finset (Fin 6)))
    (p : Finset (Fin 6) → ℝ)
    (hcard : ∀ A ∈ F, A.card = 3)
    (hmeet : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card)
    (hsum : ∑ A ∈ F, p A ≤ 1)
    (hheavy : ∀ P : Finset (Fin 6), P.card = 2 → (∀ A ∈ F, P ⊆ A) →
      3 ≤ F.card → ∀ A ∈ F, (1 : ℝ)/3 < p A) :
    (F.biUnion id).card ≤ 4 :=
  union_small_from_classification F p hcard hsum
    (LowSupportCombinatorics.triple_family_classification F hcard hmeet) hheavy

end LowSupportTypeClosure



/- Component: LowSupportRowTypes -/

open MeasureTheory

namespace LowSupportRowTypes

/-- The union of an intersecting pair family with no common element has exactly three elements. -/
theorem pair_family_union_card (F : Finset (Finset (Fin 6)))
    (hc : ∀ S ∈ F, S.card = 2)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hn : ∀ c : Fin 6, ∃ S ∈ F, c ∉ S) : (F.biUnion id).card = 3 := by
  have hm : ∀ S ∈ F, ∀ T ∈ F, ∃ c, c ∈ S ∧ c ∈ T := by
    intro S hS T hT
    obtain ⟨c,hc⟩ := hi S hS T hT
    exact ⟨c,Finset.mem_inter.mp hc⟩
  obtain ⟨a,b,c,hab,hac,hbc,hclass⟩ := LowSupportCombinatorics.intersecting_pair_family F hc hm hn
  have habF : {a,b} ∈ F := by
    obtain ⟨S,hS,hcS⟩ := hn c
    rcases hclass S hS with h | h | h
    · simpa [h] using hS
    · subst S; simp at hcS
    · subst S; simp at hcS
  have hacF : {a,c} ∈ F := by
    obtain ⟨S,hS,hbS⟩ := hn b
    rcases hclass S hS with h | h | h
    · subst S; simp at hbS
    · simpa [h] using hS
    · subst S; simp at hbS
  have he : F.biUnion id = {a,b,c} := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
      rcases hclass S hS with h | h | h <;> subst S <;>
        simp only [id_eq,Finset.mem_insert,Finset.mem_singleton] at hxS ⊢ <;> aesop
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · subst x; exact Finset.mem_biUnion.mpr ⟨{a,b},habF,by simp⟩
      · subst x; exact Finset.mem_biUnion.mpr ⟨{a,b},habF,by simp⟩
      · subst x; exact Finset.mem_biUnion.mpr ⟨{a,c},hacF,by simp⟩
  rw [he]
  simp [hab,hac,hbc]

/-- In an intersecting family with no common point, sets of size at most two are pairs. -/
theorem active_small_sets_are_pairs (F : Finset (Finset (Fin 6)))
    (hc : ∀ S ∈ F, S.card ≤ 2)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hn : ∀ c : Fin 6, ∃ S ∈ F, c ∉ S) : ∀ S ∈ F, S.card = 2 := by
  intro S hS
  have hp : 0 < S.card := by
    apply Finset.card_pos.mpr
    obtain ⟨c,hc⟩ := hi S hS S hS
    exact ⟨c,(Finset.mem_inter.mp hc).1⟩
  have hne : S.card ≠ 1 := by
    intro he
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp he
    obtain ⟨T,hT,haT⟩ := hn a
    obtain ⟨x,hx⟩ := hi S hS T hT
    have hh := Finset.mem_inter.mp hx
    have hxa : x = a := by simpa [ha] using hh.1
    exact haT (hxa ▸ hh.2)
  have hb := hc S hS
  omega

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def rowType (μ : Measure Ω) (M : Ω × Ω → Finset (Fin 6)) (x : Ω) :
    Finset (Fin 6) := (LowSupportRows.activeLabels μ M x).biUnion id

theorem measurable_rowType (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6)) (hM : Measurable M) : Measurable (rowType μ M) := by
  apply measurable_finset_iff.mpr
  intro c
  simp only [rowType,Finset.mem_biUnion,id_eq]
  apply Measurable.exists
  intro S
  exact (measurableSet_setOfPred.mp (LowSupportRows.measurableSet_active_label μ M hM S)).and measurable_const

/-- Almost every active row family consists of pairs when edge labels are pairs almost everywhere. -/
theorem ae_active_card_two (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6))
    (hc : ∀ᵐ p ∂(μ.prod μ), (M p).card = 2) :
    ∀ᵐ x ∂μ, ∀ S ∈ LowSupportRows.activeLabels μ M x, S.card = 2 := by
  filter_upwards [Measure.ae_ae_of_ae_prod hc] with x hx
  intro S hS
  have hpos := (LowSupportRows.mem_activeLabels μ M x S).mp hS
  obtain ⟨y,hy,hyc⟩ := ((frequently_ae_iff.mpr (ne_of_gt hpos)).and_eventually hx).exists
  simpa [hy] using hyc

/-- The row type has cardinality three under the active-family hypotheses from the graphon proof. -/
theorem ae_rowType_card_three (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6))
    (hc : ∀ᵐ p ∂(μ.prod μ), (M p).card = 2)
    (hi : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, (M (x,y) ∩ M (x,z)).Nonempty)
    (hn : ∀ᵐ x ∂μ, ∀ c : Fin 6, ∃ S ∈ LowSupportRows.activeLabels μ M x, c ∉ S) :
    ∀ᵐ x ∂μ, (rowType μ M x).card = 3 := by
  filter_upwards [ae_active_card_two μ M hc,hi,hn] with x hxc hxi hxn
  exact pair_family_union_card _ hxc
    (LowSupportRows.relation_on_activeLabels μ M x (fun S T => (S ∩ T).Nonempty) hxi) hxn

/-- Every actual label lies in the intersection of its endpoint row types almost everywhere. -/
theorem ae_label_subset_types (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6)) (hM : Measurable M)
    (hs : ∀ᵐ p ∂(μ.prod μ), M p = M (p.2,p.1)) :
    ∀ᵐ p ∂(μ.prod μ), M p ⊆ rowType μ M p.1 ∩ rowType μ M p.2 := by
  filter_upwards [LowSupportRows.ae_prod_active_both μ M hM hs] with p hp
  intro c hc
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨M p,hp.1,hc⟩,Finset.mem_biUnion.mpr ⟨M p,hp.2,hc⟩⟩

/-- Almost-everywhere cardinality bounds pass to all active row labels. -/
theorem ae_active_card_le_two (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6))
    (hc : ∀ᵐ p ∂(μ.prod μ), (M p).card ≤ 2) :
    ∀ᵐ x ∂μ, ∀ S ∈ LowSupportRows.activeLabels μ M x, S.card ≤ 2 := by
  filter_upwards [Measure.ae_ae_of_ae_prod hc] with x hx
  intro S hS
  have hpos := (LowSupportRows.mem_activeLabels μ M x S).mp hS
  obtain ⟨y,hy,hyc⟩ := ((frequently_ae_iff.mpr (ne_of_gt hpos)).and_eventually hx).exists
  simpa [hy] using hyc

/-- Empty and singleton active labels are excluded without a separate singleton-edge argument. -/
theorem ae_active_exact_pairs (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6))
    (hc : ∀ᵐ p ∂(μ.prod μ), (M p).card ≤ 2)
    (hi : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, (M (x,y) ∩ M (x,z)).Nonempty)
    (hn : ∀ᵐ x ∂μ, ∀ c : Fin 6, ∃ S ∈ LowSupportRows.activeLabels μ M x, c ∉ S) :
    ∀ᵐ x ∂μ, ∀ S ∈ LowSupportRows.activeLabels μ M x, S.card = 2 := by
  filter_upwards [ae_active_card_le_two μ M hc,hi,hn] with x hxc hxi hxn
  exact active_small_sets_are_pairs _ hxc
    (LowSupportRows.relation_on_activeLabels μ M x (fun S T => (S ∩ T).Nonempty) hxi) hxn

/-- The row type theorem needs only a bound of two on missing-set sizes. -/
theorem ae_rowType_card_three_of_le_two (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6))
    (hc : ∀ᵐ p ∂(μ.prod μ), (M p).card ≤ 2)
    (hi : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, (M (x,y) ∩ M (x,z)).Nonempty)
    (hn : ∀ᵐ x ∂μ, ∀ c : Fin 6, ∃ S ∈ LowSupportRows.activeLabels μ M x, c ∉ S) :
    ∀ᵐ x ∂μ, (rowType μ M x).card = 3 := by
  filter_upwards [ae_active_exact_pairs μ M hc hi hn,hi,hn] with x hxc hxi hxn
  exact pair_family_union_card _ hxc
    (LowSupportRows.relation_on_activeLabels μ M x (fun S T => (S ∩ T).Nonempty) hxi) hxn

/-- The original edge labels themselves are pairs almost everywhere. -/
theorem ae_label_card_two_of_le_two (μ : Measure Ω) [SFinite μ]
    (M : Ω × Ω → Finset (Fin 6)) (hM : Measurable M)
    (hc : ∀ᵐ p ∂(μ.prod μ), (M p).card ≤ 2)
    (hi : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, (M (x,y) ∩ M (x,z)).Nonempty)
    (hn : ∀ᵐ x ∂μ, ∀ c : Fin 6, ∃ S ∈ LowSupportRows.activeLabels μ M x, c ∉ S) :
    ∀ᵐ p ∂(μ.prod μ), (M p).card = 2 := by
  have hr := ae_active_exact_pairs μ M hc hi hn
  have hp : ∀ᵐ p ∂(μ.prod μ), ∀ S ∈ LowSupportRows.activeLabels μ M p.1, S.card = 2 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hr
  filter_upwards [hp,LowSupportRows.ae_prod_active μ M hM] with p hp ha
  exact hp (M p) ha

end LowSupportRowTypes




/- Component: LowSupportNoCommon -/
open MeasureTheory
namespace LowSupportNoCommon
open LowSupportRows

/-- A positive constant color degree prevents a common missing color in an active row family. -/
theorem no_common_missing_color {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (μ : Measure Ω) [SFinite μ]
    (W : ι → Ω × Ω → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hW0 : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p)
    (hrow : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ = δ) :
    ∀ᵐ x ∂μ, ∀ c, ∃ S ∈ activeLabels μ (missingColors W) x, c ∉ S := by
  classical
  have hr : ∀ c, ∀ᵐ x ∂μ,
      (∀ᵐ y ∂μ, 0 ≤ W c (x,y)) ∧ (∫ y, W c (x,y) ∂μ) = δ := by
    intro c
    exact (Measure.ae_ae_of_ae_prod (hW0 c)).and (hrow c)
  filter_upwards [ae_all_iff.mpr hr] with x hx
  intro c
  by_contra hnone
  push_neg at hnone
  have hz : (fun y => W c (x,y)) =ᵐ[μ] 0 := by
    filter_upwards [ae_row_active μ (missingColors W) x, (hx c).1] with y hy hnon
    have hmem : c ∈ missingColors W (x,y) := hnone _ hy
    have hn : ¬ 0 < W c (x,y) := by
      simpa [missingColors, colorSupport] using hmem
    exact le_antisymm (le_of_not_gt hn) hnon
  have hi : (∫ y, W c (x,y) ∂μ) = 0 := by
    calc
      _ = ∫ _y, (0 : ℝ) ∂μ := integral_congr_ae hz
      _ = 0 := integral_zero _ _
  linarith [(hx c).2]

end LowSupportNoCommon

/- Component: LowSupportStructure -/
open MeasureTheory
namespace LowSupportStructure

/-- The measurable type classification and balanced-row mass constraint together
leave at least one color positive almost everywhere. -/
theorem positive_color_of_types {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ = (1 : ℝ)/6)
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (hs : ∀ᵐ p ∂μ.prod μ, 2 < (Finset.univ.filter (fun c => 0 < W c p)).card)
    (T : Ω → Finset (Fin 6)) (hT : Measurable T)
    (hc : ∀ᵐ x ∂μ, (T x).card = 3)
    (hm : ∀ᵐ p ∂μ.prod μ, (LowSupportRows.missingColors W p).card = 2)
    (hsub : ∀ᵐ p ∂μ.prod μ, LowSupportRows.missingColors W p ⊆ T p.1 ∩ T p.2) :
    ∃ c : Fin 6, ∀ᵐ p ∂μ.prod μ, 0 < W c p := by
  classical
  let F := LowSupportTypeFamily.activeTypes μ T
  have hcard := LowSupportTypeFamily.activeTypes_card_three μ T hc
  have hmeet := LowSupportTypeFamily.activeTypes_inter_card μ
    (LowSupportRows.missingColors W) T hm hsub
  have hsum := LowSupportMass.sum_fiber_mass_le_one (μ := μ) T hT F
  have hsmall : (F.biUnion id).card ≤ 4 := by
    apply LowSupportTypeClosure.type_union_card_le_four F
      (fun S => μ.real {x | T x = S}) hcard hmeet hsum
    intro P hP hp _
    exact LowSupportHeavyClasses.active_class_mass_gt_of_common_pair
      μ W hW hb hr ht hs T P hP hc hm hsub hp
  have hex : ∃ c : Fin 6, c ∉ F.biUnion id := by
    by_contra h
    have he : F.biUnion id = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro c
      by_contra hc
      exact h ⟨c,hc⟩
    rw [he] at hsmall
    norm_num at hsmall
  obtain ⟨c,hc⟩ := hex
  refine ⟨c,LowSupportTypeFamily.ae_positive_of_type_container μ W T hsub
    (F.biUnion id) ?_ c hc⟩
  intro S hS i hi
  exact Finset.mem_biUnion.mpr ⟨S,hS,hi⟩

theorem positive_color_of_root_intersection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ = (1 : ℝ)/6)
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (hs : ∀ᵐ p ∂μ.prod μ, 4 ≤ (LowSupportRows.colorSupport W p).card)
    (hsymm : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hi : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      (LowSupportRows.missingColors W (x,y) ∩ LowSupportRows.missingColors W (x,z)).Nonempty) :
    ∃ c : Fin 6, ∀ᵐ p ∂μ.prod μ, 0 < W c p := by
  classical
  let M := LowSupportRows.missingColors W
  have hM : Measurable M := LowSupportRows.measurable_missingColors W hW
  have hmc : ∀ᵐ p ∂μ.prod μ, (M p).card ≤ 2 := by
    filter_upwards [hs] with p hp
    change ((LowSupportRows.colorSupport W p)ᶜ).card ≤ 2
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  have hno := LowSupportNoCommon.no_common_missing_color μ W (1/6) (by norm_num)
    (fun c => (hb c).mono (fun _ h => h.1)) hr
  let T := LowSupportRowTypes.rowType μ M
  apply positive_color_of_types μ W hW hb hr ht
    (hs.mono (fun p hp => by change 2 < (LowSupportRows.colorSupport W p).card; omega))
    T (LowSupportRowTypes.measurable_rowType μ M hM)
    (LowSupportRowTypes.ae_rowType_card_three_of_le_two μ M hmc hi hno)
    (LowSupportRowTypes.ae_label_card_two_of_le_two μ M hM hmc hi hno)
    (LowSupportRowTypes.ae_label_subset_types μ M hM (LowSupportRows.ae_missingColors_symm μ W hsymm))


end LowSupportStructure

/- Component: LowSupportAnalysis -/
open MeasureTheory
namespace LowSupportAnalysis
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_square_lower (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, f x ^ 2 ∂μ := by
  let a := ∫ x, f x ∂μ
  have hnon : 0 ≤ ∫ x, (f x - a)^2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have he : (fun x => (f x - a)^2) =
      (fun x => f x ^ 2 - (2 * a) * f x + a ^ 2) := by
    funext x
    ring
  rw [he] at hnon
  rw [integral_add (f := fun x => f x ^ 2 - (2 * a) * f x)
    (g := fun _ => a ^ 2) (hf2.sub (hf.const_mul (2*a))) (integrable_const _)] at hnon
  rw [integral_sub hf2 (hf.const_mul (2*a)), integral_const_mul] at hnon
  simp only [integral_const] at hnon
  have hμ : μ.real Set.univ = 1 := by simp
  rw [hμ] at hnon
  simp only [one_smul] at hnon
  dsimp [a] at hnon
  nlinarith

lemma integral_product_square_le (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (hg01 : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  have hp0 : 0 ≤ ∫ x, f x * g x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf01, hg01] with x hx hy
    exact mul_nonneg hx.1 hy.1
  have hpf : (∫ x, f x * g x ∂μ) ≤ ∫ x, f x ∂μ := by
    apply integral_mono_ae hfg hf
    filter_upwards [hf01, hg01] with x hx hy
    nlinarith
  have hpg : (∫ x, f x * g x ∂μ) ≤ ∫ x, g x ∂μ := by
    apply integral_mono_ae hfg hg
    filter_upwards [hf01, hg01] with x hx hy
    nlinarith
  simpa only [pow_two] using mul_le_mul hpf hpg hp0 (hp0.trans hpf)

lemma weighted_split_square_le (H h f g : Ω → ℝ)
    (hHh : Integrable (fun x => H x * h x) μ)
    (hHh2 : Integrable (fun x => (H x * h x)^2) μ)
    (hHfg : Integrable (fun x => H x * (f x * g x)) μ)
    (hH : ∀ᵐ x ∂μ, 0 ≤ H x ∧ H x ≤ 1)
    (hlocal : ∀ᵐ x ∂μ, h x ^ 2 ≤ f x * g x) :
    (∫ x, H x * h x ∂μ)^2 ≤ ∫ x, H x * (f x * g x) ∂μ := by
  apply (integral_square_lower _ hHh hHh2).trans
  apply integral_mono_ae hHh2 hHfg
  filter_upwards [hH,hlocal] with x hx hy
  have h1 : (H x)^2 ≤ H x := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (h x))
  have h3 := mul_le_mul_of_nonneg_left hy hx.1
  nlinarith [sq_nonneg (h x)]

lemma integral_mul_pos_of_pos_ae (f g : Ω → ℝ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 < g x)
    (hfpos : 0 < ∫ x, f x ∂μ) :
    0 < ∫ x, f x * g x ∂μ := by
  have hp0 : ∀ᵐ x ∂μ, 0 ≤ f x * g x := by
    filter_upwards [hf0, hg] with x hx hy
    exact mul_nonneg hx (le_of_lt hy)
  by_contra hn
  have hz : (∫ x, f x * g x ∂μ) = 0 :=
    le_antisymm (le_of_not_gt hn) (integral_nonneg_of_ae hp0)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hp0 hfg).mp hz
  have hfz : f =ᵐ[μ] 0 := by
    filter_upwards [hae, hg] with x hx hy
    exact (mul_eq_zero.mp hx).resolve_right (ne_of_gt hy)
  have hi : (∫ x, f x ∂μ) = 0 := by
    calc
      (∫ x, f x ∂μ) = ∫ x, (0 : ℝ) ∂μ := integral_congr_ae hfz
      _ = 0 := integral_zero _ _
  linarith


lemma unit_integrable {f : Ω → ℝ} (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2)

lemma integral_unit_bounds {f : Ω → ℝ} (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∫ x, f x ∂μ) ∧ (∫ x, f x ∂μ) ≤ 1 := by
  constructor
  · exact integral_nonneg (fun x => (hb x).1)
  · have hh := integral_mono (unit_integrable (μ := μ) hf hb) (integrable_const (1 : ℝ))
      (fun x => (hb x).2)
    simpa using hh

lemma mul_unit {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a*b ∧ a*b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1, (mul_le_mul ha.2 hb.2 hb.1 (by norm_num)).trans_eq (by norm_num)⟩

variable {V : Type*} [MeasurableSpace V] {ν : Measure V} [IsProbabilityMeasure ν]

/-- Splitting one integrated vertex preserves positivity, quantitatively.
The remaining vertex variables may be collected in the arbitrary probability space V. -/
lemma vertex_split_square (F G : Ω × V → ℝ) (H : V → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1)
    (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (bH : ∀ v, 0 ≤ H v ∧ H v ≤ 1) :
    (∫ v, H v * (∫ u, F (u,v)*G (u,v) ∂μ) ∂ν)^2 ≤
      ∫ v, H v * ((∫ u, F (u,v) ∂μ) * (∫ u, G (u,v) ∂μ)) ∂ν := by
  let f : V → ℝ := fun v => ∫ u, F (u,v) ∂μ
  let g : V → ℝ := fun v => ∫ u, G (u,v) ∂μ
  let h : V → ℝ := fun v => ∫ u, F (u,v)*G (u,v) ∂μ
  have fm : Measurable f := hF.stronglyMeasurable.integral_prod_left'.measurable
  have gm : Measurable g := hG.stronglyMeasurable.integral_prod_left'.measurable
  have hm : Measurable h := (hF.mul hG).stronglyMeasurable.integral_prod_left'.measurable
  have smF (v : V) : Measurable (fun u => F (u,v)) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have smG (v : V) : Measurable (fun u => G (u,v)) :=
    hG.comp (measurable_id.prodMk measurable_const)
  have bf (v : V) : 0 ≤ f v ∧ f v ≤ 1 :=
    integral_unit_bounds (smF v) (fun u => bF (u,v))
  have bg (v : V) : 0 ≤ g v ∧ g v ≤ 1 :=
    integral_unit_bounds (smG v) (fun u => bG (u,v))
  have bh (v : V) : 0 ≤ h v ∧ h v ≤ 1 :=
    integral_unit_bounds ((smF v).mul (smG v)) (fun u => mul_unit (bF (u,v)) (bG (u,v)))
  have hl (v : V) : h v ^ 2 ≤ f v * g v :=
    integral_product_square_le _ _
      (unit_integrable (smF v) (fun u => bF (u,v)))
      (unit_integrable (smG v) (fun u => bG (u,v)))
      (unit_integrable ((smF v).mul (smG v)) (fun u => mul_unit (bF (u,v)) (bG (u,v))))
      (Filter.Eventually.of_forall (fun u => bF (u,v)))
      (Filter.Eventually.of_forall (fun u => bG (u,v)))
  apply weighted_split_square_le H h f g
  · exact unit_integrable (hH.mul hm) (fun v => mul_unit (bH v) (bh v))
  · apply unit_integrable ((hH.mul hm).pow_const 2)
    intro v
    simpa only [pow_two, Pi.mul_apply] using mul_unit (mul_unit (bH v) (bh v)) (mul_unit (bH v) (bh v))
  · exact unit_integrable (hH.mul (fm.mul gm)) (fun v => mul_unit (bH v) (mul_unit (bf v) (bg v)))
  · exact Filter.Eventually.of_forall bH
  · exact Filter.Eventually.of_forall hl


lemma unit_integrable_ae {f : Ω → ℝ} (hf : Measurable f)
    (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  filter_upwards [hb] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

lemma integral_unit_bounds_ae {f : Ω → ℝ} (hf : Measurable f)
    (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∫ x, f x ∂μ) ∧ (∫ x, f x ∂μ) ≤ 1 := by
  constructor
  · exact integral_nonneg_of_ae (hb.mono (fun _ h => h.1))
  · have hh := integral_mono_ae (unit_integrable_ae (μ := μ) hf hb)
      (integrable_const (1 : ℝ)) (hb.mono (fun _ h => h.2))
    simpa using hh

lemma vertex_split_square_ae (F G : Ω × V → ℝ) (H : V → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    (bF : ∀ᵐ p ∂μ.prod ν, 0 ≤ F p ∧ F p ≤ 1)
    (bG : ∀ᵐ p ∂μ.prod ν, 0 ≤ G p ∧ G p ≤ 1)
    (bH : ∀ᵐ v ∂ν, 0 ≤ H v ∧ H v ≤ 1) :
    (∫ v, H v * (∫ u, F (u,v)*G (u,v) ∂μ) ∂ν)^2 ≤
      ∫ v, H v * ((∫ u, F (u,v) ∂μ) * (∫ u, G (u,v) ∂μ)) ∂ν := by
  let f : V → ℝ := fun v => ∫ u, F (u,v) ∂μ
  let g : V → ℝ := fun v => ∫ u, G (u,v) ∂μ
  let h : V → ℝ := fun v => ∫ u, F (u,v)*G (u,v) ∂μ
  have fm : Measurable f := hF.stronglyMeasurable.integral_prod_left'.measurable
  have gm : Measurable g := hG.stronglyMeasurable.integral_prod_left'.measurable
  have hm : Measurable h := (hF.mul hG).stronglyMeasurable.integral_prod_left'.measurable
  have smF (v : V) : Measurable (fun u => F (u,v)) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have smG (v : V) : Measurable (fun u => G (u,v)) :=
    hG.comp (measurable_id.prodMk measurable_const)
  have rowsF : ∀ᵐ v ∂ν, ∀ᵐ u ∂μ, 0 ≤ F (u,v) ∧ F (u,v) ≤ 1 := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod bF)
    exact (measurableSet_le measurable_const hF).inter (measurableSet_le hF measurable_const)
  have rowsG : ∀ᵐ v ∂ν, ∀ᵐ u ∂μ, 0 ≤ G (u,v) ∧ G (u,v) ≤ 1 := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod bG)
    exact (measurableSet_le measurable_const hG).inter (measurableSet_le hG measurable_const)
  have bf : ∀ᵐ v ∂ν, 0 ≤ f v ∧ f v ≤ 1 := rowsF.mono (fun v hv => integral_unit_bounds_ae (smF v) hv)
  have bg : ∀ᵐ v ∂ν, 0 ≤ g v ∧ g v ≤ 1 := rowsG.mono (fun v hv => integral_unit_bounds_ae (smG v) hv)
  have bh : ∀ᵐ v ∂ν, 0 ≤ h v ∧ h v ≤ 1 := by
    filter_upwards [rowsF, rowsG] with v hv hw
    apply integral_unit_bounds_ae ((smF v).mul (smG v))
    filter_upwards [hv,hw] with u hu ht
    exact mul_unit hu ht
  have hl : ∀ᵐ v ∂ν, h v ^ 2 ≤ f v * g v := by
    filter_upwards [rowsF, rowsG] with v hv hw
    apply integral_product_square_le _ _
      (unit_integrable_ae (smF v) hv) (unit_integrable_ae (smG v) hw) _ hv hw
    apply unit_integrable_ae ((smF v).mul (smG v))
    filter_upwards [hv,hw] with u hu ht
    exact mul_unit hu ht
  apply weighted_split_square_le H h f g
  · apply unit_integrable_ae (hH.mul hm)
    filter_upwards [bH,bh] with v hv hw
    exact mul_unit hv hw
  · apply unit_integrable_ae ((hH.mul hm).pow_const 2)
    filter_upwards [bH,bh] with v hv hw
    simpa only [pow_two, Pi.mul_apply] using mul_unit (mul_unit hv hw) (mul_unit hv hw)
  · apply unit_integrable_ae (hH.mul (fm.mul gm))
    filter_upwards [bH,bf,bg] with v hv hf hg
    exact mul_unit hv (mul_unit hf hg)
  · exact bH
  · exact hl

end LowSupportAnalysis



/- Component: LowSupportCycle -/
open MeasureTheory
namespace LowSupportCycle
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {τ : Measure Z}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]

lemma bounded_integrable (f : X → ℝ) (hf : Measurable f)
    (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  filter_upwards [hb] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- Swap any two blocks of latent variables, under almost-everywhere unit bounds. -/
lemma swap_blocks (f : X × Y → ℝ) (hf : Measurable f)
    (hb : ∀ᵐ p ∂μ.prod ν, 0 ≤ f p ∧ f p ≤ 1) :
    (∫ x, ∫ y, f (x,y) ∂ν ∂μ) = ∫ y, ∫ x, f (x,y) ∂μ ∂ν := by
  exact integral_integral_swap (bounded_integrable f hf hb)

/-- Reassociate a three-block integral without evaluating kernels on diagonals. -/
lemma reassociate_blocks (f : (X × Y) × Z → ℝ) (hf : Measurable f)
    (hb : ∀ᵐ p ∂(μ.prod ν).prod τ, 0 ≤ f p ∧ f p ≤ 1) :
    (∫ xy, ∫ z, f (xy,z) ∂τ ∂μ.prod ν) =
      ∫ x, ∫ y, ∫ z, f ((x,y),z) ∂τ ∂ν ∂μ := by
  exact integral_prod _ (bounded_integrable f hf hb).integral_prod_left

/-- Independent split-vertex factors expand as a product-space integral. -/
lemma separated_factors (f : X → ℝ) (g : Y → ℝ) (h : ℝ) :
    h * ((∫ x, f x ∂μ) * (∫ y, g y ∂ν)) =
      ∫ p, h * (f p.1 * g p.2) ∂μ.prod ν := by
  rw [integral_const_mul, integral_prod_mul]

/-- Three successive splitting inequalities imply the exponent-eight bound. -/
lemma three_splits {b s₁ s₂ c : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (h₁ : b^2 ≤ s₁) (h₂ : s₁^2 ≤ s₂) (h₃ : s₂^2 ≤ c) : b^8 ≤ c := by
  have h₁' : (b^2)^2 ≤ s₁^2 := pow_le_pow_left₀ (sq_nonneg b) h₁ 2
  have h₂' : ((b^2)^2)^2 ≤ s₂^2 :=
    pow_le_pow_left₀ (sq_nonneg (b^2)) (h₁'.trans h₂) 2
  simpa only [← pow_mul] using h₂'.trans h₃

lemma zero_after_three_splits {b s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (h₁ : b^2 ≤ s₁) (h₂ : s₁^2 ≤ s₂) (h₃ : s₂^2 ≤ 0) : b = 0 := by
  have h := three_splits hs₁ hs₂ h₁ h₂ h₃
  have hz : b^8 = 0 := le_antisymm h (by positivity)
  exact (pow_eq_zero_iff (by decide : (8 : ℕ) ≠ 0)).mp hz

end LowSupportCycle

open MeasureTheory



namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def doubled (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ yz, (W 1 yz * W 4 yz) *
    (∫ x, (W 0 (x,yz.1) * W 5 (yz.2,x)) *
      (W 2 (yz.2,x) * W 3 (x,yz.1)) ∂μ) ∂μ.prod μ

noncomputable def splitFirst (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ yz, ∫ xu, (W 1 yz * W 4 yz) *
    ((W 0 (xu.1,yz.1) * W 5 (yz.2,xu.1)) *
      (W 2 (yz.2,xu.2) * W 3 (xu.2,yz.1))) ∂μ.prod μ ∂μ.prod μ

/-- The first actual doubled-triangle vertex split; no symmetry is needed. -/
lemma doubled_square_le_splitFirst (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    (doubled (μ := μ) W)^2 ≤ splitFirst (μ := μ) W := by
  let F : Ω × (Ω × Ω) → ℝ := fun p => W 0 (p.1,p.2.1) * W 5 (p.2.2,p.1)
  let G : Ω × (Ω × Ω) → ℝ := fun p => W 2 (p.2.2,p.1) * W 3 (p.1,p.2.1)
  let H : Ω × Ω → ℝ := fun p => W 1 p * W 4 p
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hH : Measurable H := (hm 1).mul (hm 4)
  have h := LowSupportAnalysis.vertex_split_square (μ := μ) (ν := μ.prod μ)
    F G H hF hG hH
    (fun p => LowSupportAnalysis.mul_unit (hb 0 _) (hb 5 _))
    (fun p => LowSupportAnalysis.mul_unit (hb 2 _) (hb 3 _))
    (fun p => LowSupportAnalysis.mul_unit (hb 1 _) (hb 4 _))
  change (doubled (μ := μ) W)^2 ≤ _ at h
  apply h.trans_eq
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro yz
  exact separated_factors (μ := μ) (ν := μ)
    (fun x => F (x,yz)) (fun u => G (u,yz)) (H yz)

/-- Reordering the four-variable intermediate density to put (x,u) outside (y,z). -/
lemma splitFirst_reorder (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    splitFirst (μ := μ) W =
      ∫ xu, ∫ yz, (W 1 yz * W 4 yz) *
        ((W 0 (xu.1,yz.1) * W 5 (yz.2,xu.1)) *
          (W 2 (yz.2,xu.2) * W 3 (xu.2,yz.1))) ∂μ.prod μ ∂μ.prod μ := by
  unfold splitFirst
  apply swap_blocks (μ := μ.prod μ) (ν := μ.prod μ)
    (fun p : (Ω × Ω) × (Ω × Ω) => (W 1 p.1 * W 4 p.1) *
      ((W 0 (p.2.1,p.1.1) * W 5 (p.1.2,p.2.1)) *
        (W 2 (p.1.2,p.2.2) * W 3 (p.2.2,p.1.1))))
  · fun_prop
  · apply Filter.Eventually.of_forall
    intro p
    exact LowSupportAnalysis.mul_unit (LowSupportAnalysis.mul_unit (hb 1 _) (hb 4 _))
      (LowSupportAnalysis.mul_unit (LowSupportAnalysis.mul_unit (hb 0 _) (hb 5 _))
        (LowSupportAnalysis.mul_unit (hb 2 _) (hb 3 _)))
end LowSupportCycle
namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A one-step split in an arbitrary latent block; the integrand is concrete below. -/
lemma split_expanded {V : Type*} [MeasurableSpace V] {ν : Measure V}
    [IsProbabilityMeasure ν] (F G : Ω × V → ℝ) (H : V → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (bH : ∀ p, 0 ≤ H p ∧ H p ≤ 1) :
    (∫ v, H v * (∫ x, F (x,v)*G (x,v) ∂μ) ∂ν)^2 ≤
      ∫ v, ∫ xx, H v * (F (xx.1,v)*G (xx.2,v)) ∂μ.prod μ ∂ν := by
  apply (LowSupportAnalysis.vertex_split_square F G H hF hG hH bF bG bH).trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => separated_factors _ _ _)

noncomputable def splitSecondInput (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ p, (W 2 (p.1,p.2.2) * W 5 (p.1,p.2.1)) *
    (∫ y, (W 0 (p.2.1,y) * W 1 (y,p.1)) *
      (W 3 (p.2.2,y) * W 4 (y,p.1)) ∂μ) ∂μ.prod (μ.prod μ)
noncomputable def splitSecond (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ p, ∫ yv, (W 2 (p.1,p.2.2) * W 5 (p.1,p.2.1)) *
    ((W 0 (p.2.1,yv.1) * W 1 (yv.1,p.1)) *
      (W 3 (p.2.2,yv.2) * W 4 (yv.2,p.1))) ∂μ.prod μ ∂μ.prod (μ.prod μ)

lemma second_split (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    (splitSecondInput (μ := μ) W)^2 ≤ splitSecond (μ := μ) W := by
  apply split_expanded
    (fun p : Ω × (Ω × (Ω × Ω)) => W 0 (p.2.2.1,p.1) * W 1 (p.1,p.2.1))
    (fun p : Ω × (Ω × (Ω × Ω)) => W 3 (p.2.2.2,p.1) * W 4 (p.1,p.2.1))
    (fun p => W 2 (p.1,p.2.2) * W 5 (p.1,p.2.1))
  · fun_prop
  · fun_prop
  · fun_prop
  · exact fun p => LowSupportAnalysis.mul_unit (hb 0 _) (hb 1 _)
  · exact fun p => LowSupportAnalysis.mul_unit (hb 3 _) (hb 4 _)
  · exact fun p => LowSupportAnalysis.mul_unit (hb 2 _) (hb 5 _)

noncomputable def splitThirdInput (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ p, (W 0 (p.1.1,p.2.1) * W 3 (p.1.2,p.2.2)) *
    (∫ z, (W 1 (p.2.1,z) * W 2 (z,p.1.2)) *
      (W 4 (p.2.2,z) * W 5 (z,p.1.1)) ∂μ) ∂(μ.prod μ).prod (μ.prod μ)
noncomputable def cycleGrouped (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ p, ∫ zw, (W 0 (p.1.1,p.2.1) * W 3 (p.1.2,p.2.2)) *
    ((W 1 (p.2.1,zw.1) * W 2 (zw.1,p.1.2)) *
      (W 4 (p.2.2,zw.2) * W 5 (zw.2,p.1.1))) ∂μ.prod μ ∂(μ.prod μ).prod (μ.prod μ)

lemma third_split (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    (splitThirdInput (μ := μ) W)^2 ≤ cycleGrouped (μ := μ) W := by
  apply split_expanded
    (fun p : Ω × ((Ω × Ω) × (Ω × Ω)) => W 1 (p.2.2.1,p.1) * W 2 (p.1,p.2.1.2))
    (fun p : Ω × ((Ω × Ω) × (Ω × Ω)) => W 4 (p.2.2.2,p.1) * W 5 (p.1,p.2.1.1))
    (fun p => W 0 (p.1.1,p.2.1) * W 3 (p.1.2,p.2.2))
  · fun_prop
  · fun_prop
  · fun_prop
  · exact fun p => LowSupportAnalysis.mul_unit (hb 1 _) (hb 2 _)
  · exact fun p => LowSupportAnalysis.mul_unit (hb 4 _) (hb 5 _)
  · exact fun p => LowSupportAnalysis.mul_unit (hb 0 _) (hb 3 _)
end LowSupportCycle
namespace LowSupportCycle
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {τ : Measure Z}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]

lemma rotate_blocks (f : X × (Y × Z) → ℝ) (hf : Measurable f)
    (hb : ∀ p, 0 ≤ f p ∧ f p ≤ 1) :
    (∫ xy, ∫ z, f (xy.1,(xy.2,z)) ∂τ ∂μ.prod ν) =
      ∫ yz, ∫ x, f (x,yz) ∂μ ∂ν.prod τ := by
  have hi := LowSupportAnalysis.unit_integrable (μ := μ.prod (ν.prod τ)) hf hb
  have he := (measurePreserving_prodAssoc μ ν τ).integral_comp' f
  have hm : Measurable (fun p : (X × Y) × Z => f (p.1.1,(p.1.2,p.2))) := by fun_prop
  have hi' := LowSupportAnalysis.unit_integrable (μ := (μ.prod ν).prod τ) hm
    (fun p => hb (p.1.1,(p.1.2,p.2)))
  calc
    _ = ∫ p, f (p.1.1,(p.1.2,p.2)) ∂(μ.prod ν).prod τ := (integral_prod _ hi').symm
    _ = ∫ p, f p ∂μ.prod (ν.prod τ) := he
    _ = _ := integral_prod_symm _ hi
end LowSupportCycle
namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma first_to_second (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    splitFirst (μ := μ) W = splitSecondInput (μ := μ) W := by
  let f : Ω × (Ω × (Ω × Ω)) → ℝ := fun p =>
    (W 1 (p.1,p.2.1) * W 4 (p.1,p.2.1)) *
    ((W 0 (p.2.2.1,p.1) * W 5 (p.2.1,p.2.2.1)) *
      (W 2 (p.2.1,p.2.2.2) * W 3 (p.2.2.2,p.1)))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1 := fun p =>
    LowSupportAnalysis.mul_unit (LowSupportAnalysis.mul_unit (hb 1 _) (hb 4 _))
      (LowSupportAnalysis.mul_unit (LowSupportAnalysis.mul_unit (hb 0 _) (hb 5 _))
        (LowSupportAnalysis.mul_unit (hb 2 _) (hb 3 _)))
  have h := rotate_blocks (μ := μ) (ν := μ) (τ := μ.prod μ) f hf bf
  change splitFirst (μ := μ) W = _ at h
  apply h.trans
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp [f]
  ring

lemma second_to_third (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    splitSecond (μ := μ) W = splitThirdInput (μ := μ) W := by
  let f : Ω × ((Ω × Ω) × (Ω × Ω)) → ℝ := fun p =>
    (W 2 (p.1,p.2.1.2) * W 5 (p.1,p.2.1.1)) *
    ((W 0 (p.2.1.1,p.2.2.1) * W 1 (p.2.2.1,p.1)) *
      (W 3 (p.2.1.2,p.2.2.2) * W 4 (p.2.2.2,p.1)))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1 := fun p =>
    LowSupportAnalysis.mul_unit (LowSupportAnalysis.mul_unit (hb 2 _) (hb 5 _))
      (LowSupportAnalysis.mul_unit (LowSupportAnalysis.mul_unit (hb 0 _) (hb 1 _))
        (LowSupportAnalysis.mul_unit (hb 3 _) (hb 4 _)))
  have h := rotate_blocks (μ := μ) (ν := μ.prod μ) (τ := μ.prod μ) f hf bf
  change splitSecond (μ := μ) W = _ at h
  apply h.trans
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp [f]
  ring

lemma doubled_pow_eight_le_cycle (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    (doubled (μ := μ) W)^8 ≤ cycleGrouped (μ := μ) W := by
  have h1 := doubled_square_le_splitFirst (μ := μ) W hm hb
  have h2 := second_split (μ := μ) W hm hb
  have h3 := third_split (μ := μ) W hm hb
  rw [← first_to_second W hm hb] at h2
  rw [← second_to_third W hm hb] at h3
  exact three_splits ((sq_nonneg _).trans h1) ((sq_nonneg _).trans h2) h1 h2 h3
end LowSupportCycle
namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def cycleNested (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ x, ∫ y, ∫ z, ∫ u, ∫ v, ∫ w,
    W 0 (x,y) * W 1 (y,z) * W 2 (z,u) * W 3 (u,v) * W 4 (v,w) * W 5 (w,x)
    ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

@[fun_prop] lemma measurable_integrate {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) [SFinite ν] (f : A → B → ℝ)
    (hf : Measurable (Function.uncurry f)) : Measurable (fun a => ∫ b, f a b ∂ν) :=
  hf.stronglyMeasurable.integral_prod_right.measurable


lemma cycleGrouped_expand (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    cycleGrouped (μ := μ) W =
      ∫ x, ∫ u, ∫ y, ∫ v, ∫ z, ∫ w,
        (W 0 (x,y)*W 3 (u,v)) * ((W 1 (y,z)*W 2 (z,u)) *
          (W 4 (v,w)*W 5 (w,x))) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
  unfold cycleGrouped
  rw [integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))]
  rw [integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  dsimp only
  rw [integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  exact integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
end LowSupportCycle
namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma cycleGrouped_eq_nested (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    cycleGrouped (μ := μ) W = cycleNested (μ := μ) W := by
  rw [cycleGrouped_expand W hm hb]
  let f := fun x u y v z w => (W 0 (x,y)*W 3 (u,v)) *
    ((W 1 (y,z)*W 2 (z,u)) * (W 4 (v,w)*W 5 (w,x)))
  change (∫ x, ∫ u, ∫ y, ∫ v, ∫ z, ∫ w, f x u y v z w ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ) = _
  calc
    _ = ∫ x, ∫ y, ∫ u, ∫ v, ∫ z, ∫ w, f x u y v z w ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ x, ∫ y, ∫ u, ∫ z, ∫ v, ∫ w, f x u y v z w ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ x, ∫ y, ∫ z, ∫ u, ∫ v, ∫ w, f x u y v z w ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = cycleNested (μ := μ) W := by
      unfold cycleNested
      repeat' (apply integral_congr_ae; apply Filter.Eventually.of_forall; intro)
      dsimp [f]
      ring
end LowSupportCycle
namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma cycleNested_congr_ae (W V : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hV : ∀ i, Measurable (V i))
    (he : ∀ i, W i =ᵐ[μ.prod μ] V i) :
    cycleNested (μ := μ) W = cycleNested (μ := μ) V := by
  have hr i := Measure.ae_ae_of_ae_prod (he i)
  have hrev : ∀ᵐ x ∂μ, ∀ᵐ w ∂μ, W 5 (w,x) = V 5 (w,x) :=
    (Measure.ae_ae_comm (p := fun w x => W 5 (w,x) = V 5 (w,x)) (measurableSet_eq_fun (hW 5) (hV 5))).mp (hr 5)
  unfold cycleNested
  apply integral_congr_ae
  filter_upwards [hr 0, hrev] with x hx hx5
  apply integral_congr_ae
  filter_upwards [hx, hr 1] with y h0 hy
  apply integral_congr_ae
  filter_upwards [hy, hr 2] with z h1 hz
  apply integral_congr_ae
  filter_upwards [hz, hr 3] with u h2 hu
  apply integral_congr_ae
  filter_upwards [hu, hr 4] with v h3 hv
  apply integral_congr_ae
  filter_upwards [hv, hx5] with w h4 h5
  simp only [h0,h1,h2,h3,h4,h5]
end LowSupportCycle
namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma doubled_congr_ae (W V : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hV : ∀ i, Measurable (V i))
    (he : ∀ i, W i =ᵐ[μ.prod μ] V i) :
    doubled (μ := μ) W = doubled (μ := μ) V := by
  have hr i := Measure.ae_ae_of_ae_prod (he i)
  have hv i : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, W i (x,y) = V i (x,y) :=
    (Measure.ae_ae_comm (p := fun x y => W i (x,y) = V i (x,y)) (measurableSet_eq_fun (hW i) (hV i))).mp (hr i)
  unfold doubled
  apply integral_congr_ae
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [hv 0, hv 3, hr 1, hr 4] with y h0 h3 h1 h4
    filter_upwards [h1, h4, hr 2, hr 5] with z h1z h4z h2 h5
    rw [h1z,h4z]
    congr 1
    apply integral_congr_ae
    filter_upwards [h0,h3,h2,h5] with x hx0 hx3 hx2 hx5
    simp only [hx0,hx3,hx2,hx5]
  · apply measurableSet_eq_fun <;> fun_prop
end LowSupportCycle
namespace LowSupportCycle
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
/-- Transfer the quantitative bound from any pointwise unit-bounded representative. -/
lemma doubled_pow_eight_le_cycle_representative (W V : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hV : ∀ i, Measurable (V i))
    (hb : ∀ i p, 0 ≤ V i p ∧ V i p ≤ 1)
    (he : ∀ i, W i =ᵐ[μ.prod μ] V i) :
    (doubled (μ := μ) W)^8 ≤ cycleNested (μ := μ) W := by
  rw [doubled_congr_ae W V hW hV he, cycleNested_congr_ae W V hW hV he]
  rw [← cycleGrouped_eq_nested V hV hb]
  exact doubled_pow_eight_le_cycle V hV hb

lemma doubled_pow_eight_le_cycle_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1) :
    (doubled (μ := μ) W)^8 ≤ cycleNested (μ := μ) W := by
  let V : Fin 6 → Ω × Ω → ℝ := fun i p => max 0 (min 1 (W i p))
  have hV : ∀ i, Measurable (V i) := by intro i; dsimp [V]; fun_prop
  have bV : ∀ i p, 0 ≤ V i p ∧ V i p ≤ 1 := by
    intro i p
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have he : ∀ i, W i =ᵐ[μ.prod μ] V i := by
    intro i
    filter_upwards [hb i] with p hp
    dsimp [V]
    rw [min_eq_right hp.2, max_eq_right hp.1]
  exact doubled_pow_eight_le_cycle_representative W V hW hV bV he

lemma doubled_zero_of_cycle_zero_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hc : cycleNested (μ := μ) W = 0) : doubled (μ := μ) W = 0 := by
  have h := doubled_pow_eight_le_cycle_ae W hW hb
  rw [hc] at h
  exact (pow_eq_zero_iff (by decide : (8 : ℕ) ≠ 0)).mp
    (le_antisymm h (by positivity))
end LowSupportCycle

/- Component: LowSupportHall -/

namespace LowSupportHall

abbrev Slots := Fin 3 × Fin 2

/-- At most four slots avoid any specified one of the three support groups. -/
theorem card_slots_avoiding (i : Fin 3) :
    (Finset.univ.filter (fun p : Slots => p.1 ≠ i)).card = 4 := by
  fin_cases i <;> decide

/-- Three supports of size at least four covering six colors have a two-per-support transversal. -/
theorem exists_injective_selection (S : Fin 3 → Finset (Fin 6))
    (hsize : ∀ i, 4 ≤ (S i).card)
    (hcover : Finset.univ.biUnion S = Finset.univ) :
    ∃ f : Slots → Fin 6, Function.Injective f ∧ ∀ p, f p ∈ S p.1 := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective (fun p : Slots => S p.1)).mp
  intro s
  by_cases hsmall : s.card ≤ 4
  · by_cases hn : s.Nonempty
    · obtain ⟨p,hp⟩ := hn
      have hs : S p.1 ⊆ s.biUnion (fun q : Slots => S q.1) := by
        intro c hc
        exact Finset.mem_biUnion.mpr ⟨p,hp,hc⟩
      exact hsmall.trans ((hsize p.1).trans (Finset.card_le_card hs))
    · simp only [Finset.not_nonempty_iff_eq_empty] at hn
      simp [hn]
  · have hit : ∀ i : Fin 3, ∃ p ∈ s, p.1 = i := by
      intro i
      by_contra! hh
      have hs : s ⊆ Finset.univ.filter (fun p : Slots => p.1 ≠ i) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hh p hp
      have hc := Finset.card_le_card hs
      rw [card_slots_avoiding] at hc
      omega
    have he : s.biUnion (fun p : Slots => S p.1) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro c
      have hc : c ∈ Finset.univ.biUnion S := by rw [hcover]; simp
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨p,hp,hpi⟩ := hit i
      exact Finset.mem_biUnion.mpr ⟨p,hp,by simpa [hpi] using hi⟩
    rw [he]
    have hs := Finset.card_le_univ s
    simpa [Slots] using hs

/-- The transversal is automatically a bijection, since both finite sets have six elements. -/
theorem exists_bijective_selection (S : Fin 3 → Finset (Fin 6))
    (hsize : ∀ i, 4 ≤ (S i).card)
    (hcover : Finset.univ.biUnion S = Finset.univ) :
    ∃ f : Slots → Fin 6, Function.Bijective f ∧ ∀ p, f p ∈ S p.1 := by
  obtain ⟨f,hf,hm⟩ := exists_injective_selection S hsize hcover
  exact ⟨f,(Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simp [Slots]⟩,hm⟩

/-- Failure of selection forces a color missing from all three supports. -/
theorem common_missing_of_no_selection (S : Fin 3 → Finset (Fin 6))
    (hsize : ∀ i, 4 ≤ (S i).card)
    (hno : ¬ ∃ f : Slots → Fin 6, Function.Injective f ∧ ∀ p, f p ∈ S p.1) :
    ∃ c : Fin 6, ∀ i, c ∉ S i := by
  have hn : Finset.univ.biUnion S ≠ Finset.univ := by
    intro h
    exact hno (exists_injective_selection S hsize h)
  have hm : ∃ c : Fin 6, c ∉ Finset.univ.biUnion S := by
    by_contra! hh
    exact hn (Finset.eq_univ_iff_forall.mpr hh)
  obtain ⟨c,hc⟩ := hm
  refine ⟨c,?_⟩
  intro i hi
  exact hc (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hi⟩)

/-- Equivalent numerical form of the common-missing-color obstruction. -/
theorem union_card_le_five_of_no_selection (S : Fin 3 → Finset (Fin 6))
    (hsize : ∀ i, 4 ≤ (S i).card)
    (hno : ¬ ∃ f : Slots → Fin 6, Function.Injective f ∧ ∀ p, f p ∈ S p.1) :
    (Finset.univ.biUnion S).card ≤ 5 := by
  obtain ⟨c,hc⟩ := common_missing_of_no_selection S hsize hno
  have hs : Finset.univ.biUnion S ⊆ Finset.univ.erase c := by
    intro x hx
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    intro he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact hc i (he ▸ hi)
  have hh := Finset.card_le_card hs
  simpa using hh

end LowSupportHall


/- Component: LowSupportTriangle -/

open MeasureTheory

namespace LowSupportTriangle
variable {Ω : Type*}

/-- The doubled triangle in the canonical edge orientations, indexed by two slots per edge. -/
def doubledProduct (W : Fin 6 → Ω × Ω → ℝ) (x y z : Ω)
    (f : LowSupportHall.Slots → Fin 6) : ℝ :=
  (W (f (0,0)) (x,y) * W (f (0,1)) (x,y)) *
  (W (f (1,0)) (y,z) * W (f (1,1)) (y,z)) *
  (W (f (2,0)) (z,x) * W (f (2,1)) (z,x))

/-- Hall plus vanishing doubled products gives a common missing color pointwise. -/
theorem common_missing_of_doubled_zero (W : Fin 6 → Ω × Ω → ℝ) (x y z : Ω)
    (hxy : 4 ≤ (LowSupportRows.colorSupport W (x,y)).card)
    (hyz : 4 ≤ (LowSupportRows.colorSupport W (y,z)).card)
    (hzx : 4 ≤ (LowSupportRows.colorSupport W (z,x)).card)
    (hz : ∀ f : LowSupportHall.Slots → Fin 6, Function.Bijective f → doubledProduct W x y z f = 0) :
    ∃ c : Fin 6, c ∈ LowSupportRows.missingColors W (x,y) ∧
      c ∈ LowSupportRows.missingColors W (y,z) ∧
      c ∈ LowSupportRows.missingColors W (z,x) := by
  let S : Fin 3 → Finset (Fin 6) := ![LowSupportRows.colorSupport W (x,y),
    LowSupportRows.colorSupport W (y,z),LowSupportRows.colorSupport W (z,x)]
  have hsize : ∀ i, 4 ≤ (S i).card := by
    intro i
    fin_cases i <;> simp [S,hxy,hyz,hzx]
  have hno : ¬ ∃ f : LowSupportHall.Slots → Fin 6, Function.Injective f ∧ ∀ p, f p ∈ S p.1 := by
    rintro ⟨f,hf,hm⟩
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simp [LowSupportHall.Slots]⟩
    have h00 : 0 < W (f (0,0)) (x,y) := by simpa [S, LowSupportRows.colorSupport] using hm (0,0)
    have h01 : 0 < W (f (0,1)) (x,y) := by simpa [S, LowSupportRows.colorSupport] using hm (0,1)
    have h10 : 0 < W (f (1,0)) (y,z) := by simpa [S, LowSupportRows.colorSupport] using hm (1,0)
    have h11 : 0 < W (f (1,1)) (y,z) := by simpa [S, LowSupportRows.colorSupport] using hm (1,1)
    have h20 : 0 < W (f (2,0)) (z,x) := by simpa [S, LowSupportRows.colorSupport] using hm (2,0)
    have h21 : 0 < W (f (2,1)) (z,x) := by simpa [S, LowSupportRows.colorSupport] using hm (2,1)
    have hp : 0 < doubledProduct W x y z f := by unfold doubledProduct; positivity
    exact (ne_of_gt hp) (hz f hbij)
  obtain ⟨c,hc⟩ := LowSupportHall.common_missing_of_no_selection S hsize hno
  refine ⟨c,?_,?_,?_⟩
  · simpa [S,LowSupportRows.missingColors] using hc 0
  · simpa [S,LowSupportRows.missingColors] using hc 1
  · simpa [S,LowSupportRows.missingColors] using hc 2

/-- Explicit finite reindexing from canonical color permutations to support slots. -/
theorem slot_products_zero_of_permutations (W : Fin 6 → Ω × Ω → ℝ) (x y z : Ω)
    (hz : ∀ σ : Equiv.Perm (Fin 6),
      (W (σ 1) (y,z) * W (σ 4) (y,z)) *
      ((W (σ 0) (x,y) * W (σ 5) (z,x)) *
       (W (σ 2) (z,x) * W (σ 3) (x,y))) = 0) :
    ∀ f : LowSupportHall.Slots → Fin 6, Function.Bijective f → doubledProduct W x y z f = 0 := by
  intro f hf
  let e : LowSupportHall.Slots ≃ Fin 6 := (Equiv.prodComm (Fin 3) (Fin 2)).trans finProdFinEquiv
  let σ : Equiv.Perm (Fin 6) := e.symm.trans (Equiv.ofBijective f hf)
  have h := hz σ
  change (W (f (1,0)) (y,z) * W (f (1,1)) (y,z)) *
    ((W (f (0,0)) (x,y) * W (f (2,1)) (z,x)) *
     (W (f (2,0)) (z,x) * W (f (0,1)) (x,y))) = 0 at h
  unfold doubledProduct
  nlinarith only [h]

variable [MeasurableSpace Ω]

/-- Product support bounds and a.e. doubled-product vanishing give the rooted missing-pair relation. -/
theorem ae_root_missing_intersection (μ : Measure Ω) [SFinite μ]
    (W : Fin 6 → Ω × Ω → ℝ)
    (hsize : ∀ᵐ p ∂(μ.prod μ), 4 ≤ (LowSupportRows.colorSupport W p).card)
    (hsym : ∀ i, ∀ᵐ p ∂(μ.prod μ), W i p = W i (p.2,p.1))
    (hz : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      ∀ f : LowSupportHall.Slots → Fin 6, Function.Bijective f → doubledProduct W x y z f = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      (LowSupportRows.missingColors W (x,y) ∩ LowSupportRows.missingColors W (x,z)).Nonempty := by
  have hrows := Measure.ae_ae_of_ae_prod hsize
  have hsrows := Measure.ae_ae_of_ae_prod (LowSupportRows.ae_colorSupport_symm μ W hsym)
  have hmrows := Measure.ae_ae_of_ae_prod (LowSupportRows.ae_missingColors_symm μ W hsym)
  filter_upwards [hrows,hsrows,hmrows,hz] with x hx hxs hxm hxz
  filter_upwards [hx,hrows,hxz] with y hxy hy hyz
  filter_upwards [hx,hy,hxs,hxm,hyz] with z hxz hyz hs hm hzero
  have hzx : 4 ≤ (LowSupportRows.colorSupport W (z,x)).card := by rw [← hs]; exact hxz
  obtain ⟨c,hcxy,_,hczx⟩ := common_missing_of_doubled_zero W x y z hxy hyz hzx hzero
  exact ⟨c,Finset.mem_inter.mpr ⟨hcxy,by rw [hm]; exact hczx⟩⟩


/-- Canonical permutation-indexed vanishing suffices for the row-family relation. -/
theorem ae_root_missing_intersection_of_permutations (μ : Measure Ω) [SFinite μ]
    (W : Fin 6 → Ω × Ω → ℝ)
    (hsize : ∀ᵐ p ∂(μ.prod μ), 4 ≤ (LowSupportRows.colorSupport W p).card)
    (hsym : ∀ i, ∀ᵐ p ∂(μ.prod μ), W i p = W i (p.2,p.1))
    (hz : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ σ : Equiv.Perm (Fin 6),
      (W (σ 1) (y,z) * W (σ 4) (y,z)) *
      ((W (σ 0) (x,y) * W (σ 5) (z,x)) *
       (W (σ 2) (z,x) * W (σ 3) (x,y))) = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      (LowSupportRows.missingColors W (x,y) ∩ LowSupportRows.missingColors W (x,z)).Nonempty := by
  apply ae_root_missing_intersection μ W hsize hsym
  filter_upwards [hz] with x hx
  filter_upwards [hx] with y hy
  filter_upwards [hy] with z h
  exact slot_products_zero_of_permutations W x y z h

end LowSupportTriangle



/- Component: LowSupportTriangleZero -/

open MeasureTheory
namespace LowSupportTriangleZero
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def triangleProduct (W : Fin 6 → Ω × Ω → ℝ) (x y z : Ω) : ℝ :=
  (W 1 (y,z) * W 4 (y,z)) *
    ((W 0 (x,y) * W 5 (z,x)) * (W 2 (z,x) * W 3 (x,y)))

lemma triangle_zero_of_doubled_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : LowSupportCycle.doubled (μ := μ) W = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, triangleProduct W x y z = 0 := by
  let F : Ω × (Ω × Ω) → ℝ := fun p => triangleProduct W p.1 p.2.1 p.2.2
  have hF : Measurable F := by dsimp [F,triangleProduct]; fun_prop
  have bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1 := by
    intro p
    exact LowSupportAnalysis.mul_unit
      (LowSupportAnalysis.mul_unit (hb 1 _) (hb 4 _))
      (LowSupportAnalysis.mul_unit
        (LowSupportAnalysis.mul_unit (hb 0 _) (hb 5 _))
        (LowSupportAnalysis.mul_unit (hb 2 _) (hb 3 _)))
  have iF : Integrable F (μ.prod (μ.prod μ)) :=
    LowSupportAnalysis.unit_integrable hF bF
  have hi : (∫ p, F p ∂μ.prod (μ.prod μ)) = 0 := by
    rw [integral_prod _ iF, integral_integral_swap iF]
    change (∫ yz, ∫ x, (W 1 yz * W 4 yz) *
      ((W 0 (x,yz.1) * W 5 (yz.2,x)) *
       (W 2 (yz.2,x) * W 3 (x,yz.1))) ∂μ ∂μ.prod μ) = 0
    simp_rw [integral_const_mul]
    exact hz
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun p => (bF p).1)) iF).mp hi
  have hh := Measure.ae_ae_of_ae_prod hae
  filter_upwards [hh] with x hx
  exact Measure.ae_ae_of_ae_prod hx

lemma triangleProduct_congr_ae (W V : Fin 6 → Ω × Ω → ℝ)
    (hmW : ∀ i, Measurable (W i)) (hmV : ∀ i, Measurable (V i))
    (he : ∀ i, W i =ᵐ[μ.prod μ] V i) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      triangleProduct W x y z = triangleProduct V x y z := by
  have hr i := Measure.ae_ae_of_ae_prod (he i)
  have hs i : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, W i (z,x) = V i (z,x) :=
    (Measure.ae_ae_comm (p := fun z x => W i (z,x) = V i (z,x))
      (measurableSet_eq_fun (hmW i) (hmV i))).mp (hr i)
  filter_upwards [hr 0,hr 3,hs 2,hs 5] with x h0 h3 h2 h5
  filter_upwards [h0,h3,hr 1,hr 4] with y h0 h3 h1 h4
  filter_upwards [h1,h4,h2,h5] with z h1 h4 h2 h5
  simp only [triangleProduct,h0,h1,h2,h3,h4,h5]

lemma triangle_zero_of_doubled_zero_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : LowSupportCycle.doubled (μ := μ) W = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, triangleProduct W x y z = 0 := by
  let V : Fin 6 → Ω × Ω → ℝ := fun i p => max 0 (min 1 (W i p))
  have hV : ∀ i, Measurable (V i) := by intro i; dsimp [V]; fun_prop
  have bV : ∀ i p, 0 ≤ V i p ∧ V i p ≤ 1 := by
    intro i p
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have he : ∀ i, W i =ᵐ[μ.prod μ] V i := by
    intro i
    filter_upwards [hb i] with p hp
    dsimp [V]
    rw [min_eq_right hp.2, max_eq_right hp.1]
  have hzV : LowSupportCycle.doubled (μ := μ) V = 0 := by
    rw [← LowSupportCycle.doubled_congr_ae W V hm hV he]
    exact hz
  have hv := triangle_zero_of_doubled_zero V hV bV hzV
  have heq := triangleProduct_congr_ae W V hm hV he
  filter_upwards [hv,heq] with x hx ex
  filter_upwards [hx,ex] with y hy ey
  filter_upwards [hy,ey] with z hz ez
  exact ez.trans hz

lemma all_permutations_triangle_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.doubled (μ := μ) (fun i => W (σ i)) = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ σ : Equiv.Perm (Fin 6),
      triangleProduct (fun i => W (σ i)) x y z = 0 := by
  have h σ := triangle_zero_of_doubled_zero_ae (fun i => W (σ i))
    (fun i => hm (σ i)) (fun i => hb (σ i)) (hz σ)
  have ha := (ae_all_iff).mpr h
  filter_upwards [ha] with x hx
  have hy := (ae_all_iff).mpr hx
  filter_upwards [hy] with y hy
  exact (ae_all_iff).mpr hy

lemma root_missing_intersection_of_doubled_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hsize : ∀ᵐ p ∂μ.prod μ, 4 ≤ (LowSupportRows.colorSupport W p).card)
    (hsym : ∀ i, ∀ᵐ p ∂μ.prod μ, W i p = W i (p.2,p.1))
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.doubled (μ := μ) (fun i => W (σ i)) = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      (LowSupportRows.missingColors W (x,y) ∩ LowSupportRows.missingColors W (x,z)).Nonempty := by
  exact LowSupportTriangle.ae_root_missing_intersection_of_permutations μ W hsize hsym
    (all_permutations_triangle_zero W hm hb hz)

end LowSupportTriangleZero

/- Component: LowSupportPaths -/

open MeasureTheory
namespace LowSupportPathKernels

noncomputable def pathMass {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ι → Ω × Ω → ℝ) : List ι → Ω → ℝ
  | [], _ => 1
  | a :: cs, x => ∫ y, W a (x, y) * pathMass μ W cs y ∂μ

theorem pathMass_eq_ae {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ι → Ω × Ω → ℝ) (δ : ℝ)
    (hrow : ∀ a, ∀ᵐ x ∂μ, ∫ y, W a (x,y) ∂μ = δ) (cs : List ι) :
    ∀ᵐ x ∂μ, pathMass μ W cs x = δ ^ cs.length := by
  induction cs with
  | nil => simp [pathMass]
  | cons a cs ih =>
    filter_upwards [hrow a] with x hx
    change (∫ y, W a (x,y) * pathMass μ W cs y ∂μ) = δ ^ (cs.length + 1)
    calc
      _ = ∫ y, W a (x,y) * δ ^ cs.length ∂μ := by
        apply integral_congr_ae
        filter_upwards [ih] with y hy
        rw [hy]
      _ = δ * δ ^ cs.length := by rw [integral_mul_const, hx]
      _ = δ ^ (cs.length + 1) := by rw [pow_succ]; ring

theorem integral_pathMass {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ) (δ : ℝ)
    (hrow : ∀ a, ∀ᵐ x ∂μ, ∫ y, W a (x,y) ∂μ = δ) (cs : List ι) :
    ∫ x, pathMass μ W cs x ∂μ = δ ^ cs.length := by
  rw [integral_congr_ae (pathMass_eq_ae μ W δ hrow cs)]
  simp

theorem measurable_pathMass {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a)) (cs : List ι) :
    Measurable (pathMass μ W cs) := by
  induction cs with
  | nil => exact measurable_const
  | cons a cs ih =>
    exact ((hW a).mul (ih.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable


noncomputable def pathKernel {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ι → Ω × Ω → ℝ) : List ι → Ω × Ω → ℝ
  | [], _ => 0
  | [a], p => W a p
  | a :: b :: cs, p => ∫ z, W a (p.1,z) * pathKernel μ W (b :: cs) (z,p.2) ∂μ

theorem measurable_pathKernel {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a)) (cs : List ι) :
    Measurable (pathKernel μ W cs) := by
  induction cs with
  | nil => exact measurable_const
  | cons a cs ih =>
    cases cs with
    | nil => exact hW a
    | cons b cs =>
      exact (((hW a).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        (ih.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).stronglyMeasurable.integral_prod_right'.measurable

theorem pathKernel_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a))
    (hb : ∀ a p, 0 ≤ W a p ∧ W a p ≤ 1) (cs : List ι) (p : Ω × Ω) :
    0 ≤ pathKernel μ W cs p ∧ pathKernel μ W cs p ≤ 1 := by
  induction cs generalizing p with
  | nil => simp [pathKernel]
  | cons a cs ih =>
    cases cs with
    | nil => exact hb a p
    | cons b cs =>
      have hm : Measurable (fun z => W a (p.1,z) * pathKernel μ W (b :: cs) (z,p.2)) :=
        ((hW a).comp (measurable_const.prodMk measurable_id)).mul
          ((measurable_pathKernel μ W hW (b :: cs)).comp (measurable_id.prodMk measurable_const))
      have hbound (z : Ω) : 0 ≤ W a (p.1,z) * pathKernel μ W (b :: cs) (z,p.2) ∧
          W a (p.1,z) * pathKernel μ W (b :: cs) (z,p.2) ≤ 1 := by
        constructor
        · exact mul_nonneg (hb a _).1 (ih _).1
        · nlinarith [(hb a (p.1,z)).1, (hb a (p.1,z)).2, (ih (z,p.2)).1, (ih (z,p.2)).2]
      have hi : Integrable (fun z => W a (p.1,z) * pathKernel μ W (b :: cs) (z,p.2)) μ :=
        (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hbound z).1]; exact (hbound z).2))
      constructor
      · exact integral_nonneg (fun z => (hbound z).1)
      · change (∫ z, W a (p.1,z) * pathKernel μ W (b :: cs) (z,p.2) ∂μ) ≤ 1
        calc
          _ ≤ ∫ _, (1 : ℝ) ∂μ := integral_mono hi (integrable_const _) (fun z => (hbound z).2)
          _ = 1 := by simp


theorem pathKernel_row {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a))
    (hb : ∀ a p, 0 ≤ W a p ∧ W a p ≤ 1) (δ : ℝ)
    (hrow : ∀ a, ∀ᵐ x ∂μ, ∫ y, W a (x,y) ∂μ = δ)
    (cs : List ι) (hne : cs ≠ []) :
    ∀ᵐ x ∂μ, ∫ y, pathKernel μ W cs (x,y) ∂μ = δ ^ cs.length := by
  induction cs with
  | nil => exact False.elim (hne rfl)
  | cons a cs ih =>
    cases cs with
    | nil => simpa [pathKernel] using hrow a
    | cons b cs =>
      have ht := ih (by simp)
      filter_upwards [hrow a] with x hx
      have hm : Measurable (fun p : Ω × Ω => W a (x,p.1) * pathKernel μ W (b :: cs) p) :=
        ((hW a).comp (measurable_const.prodMk measurable_fst)).mul
          (measurable_pathKernel μ W hW (b :: cs))
      have hi : Integrable (fun p : Ω × Ω => W a (x,p.1) * pathKernel μ W (b :: cs) p) (μ.prod μ) := by
        apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
        apply Filter.Eventually.of_forall
        intro p
        have hk := pathKernel_bounds μ W hW hb (b :: cs) p
        have hw := hb a (x,p.1)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw.1 hk.1)]
        nlinarith
      change (∫ y, ∫ z, W a (x,z) * pathKernel μ W (b :: cs) (z,y) ∂μ ∂μ) = _
      rw [← integral_integral_swap hi]
      calc
        _ = ∫ z, W a (x,z) * δ ^ (b :: cs).length ∂μ := by
          apply integral_congr_ae
          filter_upwards [ht] with z hz
          rw [integral_const_mul, hz]
        _ = δ * δ ^ (b :: cs).length := by rw [integral_mul_const, hx]
        _ = δ ^ (a :: b :: cs).length := by simp only [List.length_cons, pow_succ]; ring

end LowSupportPathKernels



/- Component: LowSupportRepresentatives -/

open MeasureTheory
namespace LowSupportKernelRepresentatives
open LowSupportPathKernels

noncomputable def clip (f : α → ℝ) (x : α) : ℝ := max 0 (min 1 (f x))

theorem clip_bounds (f : α → ℝ) (x : α) : 0 ≤ clip f x ∧ clip f x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem measurable_clip [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable (clip f) := measurable_const.max (measurable_const.min hf)

theorem clip_eq_ae [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) : clip f =ᵐ[μ] f := by
  filter_upwards [hb] with x hx
  simp [clip, min_eq_right hx.2, max_eq_right hx.1]

theorem row_integral_congr {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {F G : Ω × Ω → ℝ}
    (h : F =ᵐ[μ.prod μ] G) :
    ∀ᵐ x ∂μ, (∫ y, F (x,y) ∂μ) = ∫ y, G (x,y) ∂μ := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  exact integral_congr_ae hx

theorem clip_row {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (F : Ω × Ω → ℝ) (δ : ℝ)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ F p ∧ F p ≤ 1)
    (hr : ∀ᵐ x ∂μ, ∫ y, F (x,y) ∂μ = δ) :
    ∀ᵐ x ∂μ, ∫ y, clip F (x,y) ∂μ = δ := by
  filter_upwards [row_integral_congr μ (clip_eq_ae (μ.prod μ) F hb), hr] with x hx hrx
  exact hx.trans hrx

noncomputable def convolution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F G : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  ∫ z, F (p.1,z) * G (z,p.2) ∂μ

theorem measurable_convolution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {F G : Ω × Ω → ℝ}
    (hF : Measurable F) (hG : Measurable G) : Measurable (convolution μ F G) :=
  ((hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
    (hG.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).stronglyMeasurable.integral_prod_right'.measurable

theorem convolution_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {F F' G G' : Ω × Ω → ℝ}
    (hF : Measurable F) (hF' : Measurable F')
    (hG : Measurable G) (hG' : Measurable G')
    (heF : F =ᵐ[μ.prod μ] F') (heG : G =ᵐ[μ.prod μ] G') :
    convolution μ F G =ᵐ[μ.prod μ] convolution μ F' G' := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (measurable_convolution μ hF hG) (measurable_convolution μ hF' hG'))).2
  have hg : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, G (z,y) = G' (z,y) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq heG)
  filter_upwards [Measure.ae_ae_of_ae_prod heF] with x hx
  filter_upwards [hg] with y hy
  apply integral_congr_ae
  filter_upwards [hx, hy] with z hz hz'
  rw [hz, hz']

theorem pathKernel_congr_ae {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {W V : ι → Ω × Ω → ℝ}
    (hW : ∀ a, Measurable (W a)) (hV : ∀ a, Measurable (V a))
    (he : ∀ a, W a =ᵐ[μ.prod μ] V a) (cs : List ι) :
    pathKernel μ W cs =ᵐ[μ.prod μ] pathKernel μ V cs := by
  induction cs with
  | nil => exact Filter.EventuallyEq.rfl
  | cons a cs ih =>
    cases cs with
    | nil => exact he a
    | cons b cs =>
      exact convolution_congr_ae μ (hW a) (hV a)
        (measurable_pathKernel μ W hW (b :: cs))
        (measurable_pathKernel μ V hV (b :: cs)) (he a) ih


/-- The nonempty path row formula under the canonical a.e. bounds. -/
theorem pathKernel_row_ae_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a))
    (hb : ∀ a, ∀ᵐ p ∂μ.prod μ, 0 ≤ W a p ∧ W a p ≤ 1) (δ : ℝ)
    (hr : ∀ a, ∀ᵐ x ∂μ, ∫ y, W a (x,y) ∂μ = δ)
    (cs : List ι) (hne : cs ≠ []) :
    ∀ᵐ x ∂μ, ∫ y, pathKernel μ W cs (x,y) ∂μ = δ ^ cs.length := by
  have he := pathKernel_congr_ae μ (fun a => measurable_clip (hW a)) hW
    (fun a => clip_eq_ae (μ.prod μ) (W a) (hb a)) cs
  have hc := pathKernel_row μ (fun a => clip (W a))
    (fun a => measurable_clip (hW a)) (fun a p => clip_bounds (W a) p) δ
    (fun a => clip_row μ (W a) δ (hb a) (hr a)) cs hne
  filter_upwards [row_integral_congr μ he, hc] with x hx hcx
  exact hx.symm.trans hcx

/-- Boundedness likewise transfers to the original representatives a.e. -/
theorem pathKernel_bounds_ae {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a))
    (hb : ∀ a, ∀ᵐ p ∂μ.prod μ, 0 ≤ W a p ∧ W a p ≤ 1) (cs : List ι) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ pathKernel μ W cs p ∧ pathKernel μ W cs p ≤ 1 := by
  have he := pathKernel_congr_ae μ (fun a => measurable_clip (hW a)) hW
    (fun a => clip_eq_ae (μ.prod μ) (W a) (hb a)) cs
  filter_upwards [he] with p hp
  rw [← hp]
  exact pathKernel_bounds μ (fun a => clip (W a))
    (fun a => measurable_clip (hW a)) (fun a p => clip_bounds (W a) p) cs p

end LowSupportKernelRepresentatives


/- Component: LowSupportPositiveCycle -/

open MeasureTheory
namespace LowSupportPositiveClosing
open LowSupportPathKernels LowSupportKernelRepresentatives

/-- The endpoint path kernel is integrable under the canonical a.e. bounds. -/
theorem integrable_pathKernel {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a))
    (hb : ∀ a, ∀ᵐ p ∂μ.prod μ, 0 ≤ W a p ∧ W a p ≤ 1) (cs : List ι) :
    Integrable (pathKernel μ W cs) (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_pathKernel μ W hW cs).aestronglyMeasurable
  filter_upwards [pathKernel_bounds_ae μ W hW hb cs] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
  exact hp.2

/-- Integrating both endpoints gives the regular path mass. -/
theorem integral_pathKernel {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a))
    (hb : ∀ a, ∀ᵐ p ∂μ.prod μ, 0 ≤ W a p ∧ W a p ≤ 1) (δ : ℝ)
    (hr : ∀ a, ∀ᵐ x ∂μ, ∫ y, W a (x,y) ∂μ = δ)
    (cs : List ι) (hne : cs ≠ []) :
    ∫ p, pathKernel μ W cs p ∂μ.prod μ = δ ^ cs.length := by
  rw [integral_prod _ (integrable_pathKernel μ W hW hb cs)]
  rw [integral_congr_ae (pathKernel_row_ae_bounds μ W hW hb δ hr cs hne)]
  simp

/-- A universally positive closing kernel cannot annihilate a positive regular path mass.
No distinctness or symmetry is needed for this analytic fact. -/
theorem closing_integral_pos {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω × Ω → ℝ)
    (hW : ∀ a, Measurable (W a))
    (hb : ∀ a, ∀ᵐ p ∂μ.prod μ, 0 ≤ W a p ∧ W a p ≤ 1) (δ : ℝ)
    (hδ : 0 < δ) (hr : ∀ a, ∀ᵐ x ∂μ, ∫ y, W a (x,y) ∂μ = δ)
    (cs : List ι) (hne : cs ≠ []) (c : ι)
    (hc : ∀ᵐ p ∂μ.prod μ, 0 < W c p) :
    0 < ∫ p, pathKernel μ W cs p * W c (p.2,p.1) ∂μ.prod μ := by
  have hswap : Measure.QuasiMeasurePreserving (Prod.swap : Ω × Ω → Ω × Ω) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving
  have hbc : ∀ᵐ p ∂μ.prod μ, 0 ≤ W c (p.2,p.1) ∧ W c (p.2,p.1) ≤ 1 :=
    hswap.ae (hb c)
  have hpc : ∀ᵐ p ∂μ.prod μ, 0 < W c (p.2,p.1) := hswap.ae hc
  have hk := pathKernel_bounds_ae μ W hW hb cs
  have hm : Measurable (fun p => pathKernel μ W cs p * W c (p.2,p.1)) :=
    (measurable_pathKernel μ W hW cs).mul ((hW c).comp measurable_swap)
  have hi : Integrable (fun p => pathKernel μ W cs p * W c (p.2,p.1)) (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [hk, hbc] with p hp hq
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.1 hq.1)]
    nlinarith
  apply LowSupportAnalysis.integral_mul_pos_of_pos_ae _ _ hi (hk.mono (fun _ hp => hp.1)) hpc
  rw [integral_pathKernel μ W hW hb δ hr cs hne]
  exact pow_pos hδ _

end LowSupportPositiveClosing


/- Component: LowSupportCyclePath -/
open MeasureTheory
namespace LowSupportCyclePath
open LowSupportPathKernels LowSupportKernelRepresentatives
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def closing (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ p, pathKernel μ W [0,1,2,3,4] p * W 5 (p.2,p.1) ∂μ.prod μ

lemma closing_eq_cycle_pointwise (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    closing (μ := μ) W = LowSupportCycle.cycleNested (μ := μ) W := by
  unfold closing
  have hp : Measurable (fun p => pathKernel μ W [0,1,2,3,4] p * W 5 (p.2,p.1)) :=
    (measurable_pathKernel μ W hW _).mul ((hW 5).comp measurable_swap)
  have bp : ∀ p, 0 ≤ pathKernel μ W [0,1,2,3,4] p * W 5 (p.2,p.1) ∧
      pathKernel μ W [0,1,2,3,4] p * W 5 (p.2,p.1) ≤ 1 :=
    fun p => LowSupportAnalysis.mul_unit (pathKernel_bounds μ W hW hb _ p) (hb 5 _)
  rw [integral_prod _ (LowSupportAnalysis.unit_integrable hp bp)]
  simp_rw [pathKernel, ← integral_const_mul, ← integral_mul_const]
  let f := fun x w y z u v => W 0 (x,y) * (W 1 (y,z) * (W 2 (z,u) *
    (W 3 (u,v) * W 4 (v,w)))) * W 5 (w,x)
  change (∫ x, ∫ w, ∫ y, ∫ z, ∫ u, ∫ v, f x w y z u v ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ) = _
  calc
    _ = ∫ x, ∫ y, ∫ w, ∫ z, ∫ u, ∫ v, f x w y z u v ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ x, ∫ y, ∫ z, ∫ w, ∫ u, ∫ v, f x w y z u v ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ x, ∫ y, ∫ z, ∫ u, ∫ w, ∫ v, f x w y z u v ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ x, ∫ y, ∫ z, ∫ u, ∫ v, ∫ w, f x w y z u v ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = LowSupportCycle.cycleNested (μ := μ) W := by
      unfold LowSupportCycle.cycleNested
      repeat' (apply integral_congr_ae; apply Filter.Eventually.of_forall; intro)
      dsimp [f]
      ring
end LowSupportCyclePath
namespace LowSupportCyclePath
open LowSupportPathKernels LowSupportKernelRepresentatives
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma closing_congr_ae (W V : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hV : ∀ i, Measurable (V i))
    (he : ∀ i, W i =ᵐ[μ.prod μ] V i) :
    closing (μ := μ) W = closing (μ := μ) V := by
  have hp := pathKernel_congr_ae μ hW hV he [0,1,2,3,4]
  have hs : ∀ᵐ p ∂μ.prod μ, W 5 (p.2,p.1) = V 5 (p.2,p.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae (he 5)
  apply integral_congr_ae
  filter_upwards [hp,hs] with p hp hs
  simp only [hp,hs]

lemma closing_eq_cycle_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1) :
    closing (μ := μ) W = LowSupportCycle.cycleNested (μ := μ) W := by
  let V := fun i => clip (W i)
  have hV : ∀ i, Measurable (V i) := fun i => measurable_clip (hW i)
  have he : ∀ i, W i =ᵐ[μ.prod μ] V i := fun i => (clip_eq_ae _ _ (hb i)).symm
  rw [closing_congr_ae W V hW hV he, LowSupportCycle.cycleNested_congr_ae W V hW hV he]
  exact closing_eq_cycle_pointwise V hV (fun i p => clip_bounds (W i) p)

lemma permutation_last (c : Fin 6) : ∃ σ : Equiv.Perm (Fin 6), σ 5 = c :=
  ⟨Equiv.swap 5 c, by simp⟩
end LowSupportCyclePath

/- Component: LowSupportAssembly -/

open MeasureTheory
open scoped BigOperators

namespace Submissions.E811LowSupport.Complete

noncomputable def supportSize {Ω : Type*} (W : Fin 6 → Ω × Ω → ℝ)
    (p : Ω × Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c => 0 < W c p)).card

/-- Ordered rainbow six-cycle density, allowing repeated sampled points. -/
noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₄) *
    W (σ 4) (x₄, x₅) * W (σ 5) (x₅, x₀)
    ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

/-- A balanced zero-rainbow-C6 six-color probability kernel has positive
product measure of cells on which at most three colors are positive. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 6 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂(μ.prod μ), ∑ c : Fin 6, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x, y) ∂μ = (1 : ℝ) / 6) →
      (∀ σ : Equiv.Perm (Fin 6), cycleDensity μ W σ = 0) →
      0 < (μ.prod μ) {p | supportSize W p ≤ 3}

/-- The exact published low-support proposition, proved from the local verified modules. -/
theorem target : statement := by
  intro Ω _ μ hμ W hm hb hsym hsum hrow hcycle
  let : IsProbabilityMeasure μ := hμ
  classical
  by_contra hn
  have hz : (μ.prod μ) {p | supportSize W p ≤ 3} = 0 :=
    le_antisymm (le_of_not_gt hn) zero_le
  have hs : ∀ᵐ p ∂μ.prod μ, 4 ≤ (LowSupportRows.colorSupport W p).card := by
    have ha := (measure_eq_zero_iff_ae_notMem).mp hz
    filter_upwards [ha] with p hp
    change ¬ supportSize W p ≤ 3 at hp
    change 4 ≤ supportSize W p
    omega
  have hd : ∀ σ : Equiv.Perm (Fin 6),
      LowSupportCycle.doubled (μ := μ) (fun i => W (σ i)) = 0 := by
    intro σ
    apply LowSupportCycle.doubled_zero_of_cycle_zero_ae
      (fun i => W (σ i)) (fun i => hm (σ i)) (fun i => hb (σ i))
    exact hcycle σ
  have hroot := LowSupportTriangleZero.root_missing_intersection_of_doubled_zero
    W hm hb hs hsym hd
  obtain ⟨c,hc⟩ := LowSupportStructure.positive_color_of_root_intersection
    μ W hm hb hrow hsum hs hsym hroot
  obtain ⟨σ,hσ⟩ := LowSupportCyclePath.permutation_last c
  have hp : ∀ᵐ p ∂μ.prod μ, 0 < W (σ 5) p := by simpa [hσ] using hc
  have hpos := LowSupportPositiveClosing.closing_integral_pos
    μ (fun i => W (σ i)) (fun i => hm (σ i)) (fun i => hb (σ i))
    (1/6) (by norm_num) (fun i => hrow (σ i)) [0,1,2,3,4] (by simp) 5 hp
  change 0 < LowSupportCyclePath.closing (μ := μ) (fun i => W (σ i)) at hpos
  rw [LowSupportCyclePath.closing_eq_cycle_ae
    (fun i => W (σ i)) (fun i => hm (σ i)) (fun i => hb (σ i))] at hpos
  have hzcycle : LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i)) = 0 := hcycle σ
  rw [hzcycle] at hpos
  exact (lt_irrefl 0) hpos

end Submissions.E811LowSupport.Complete


#print axioms Submissions.E811LowSupport.Complete.target
