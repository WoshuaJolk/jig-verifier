import Mathlib
namespace Submissions.E811FourColorParity.Complete
end Submissions.E811FourColorParity.Complete

-- Module: FourColorKernels
open MeasureTheory
namespace FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def comp (μ : Measure Ω) (f g : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  ∫ z, f (p.1,z)*g (z,p.2) ∂μ

lemma measurable_comp (μ : Measure Ω) [SFinite μ] (f g : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (comp μ f g) := by
  exact ((hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
    (hg.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).stronglyMeasurable.integral_prod_right'.measurable

lemma unit_integrable (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2)

lemma mul_unit {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a*b ∧ a*b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1, (mul_le_mul ha.2 hb.2 hb.1 (by norm_num)).trans_eq (by norm_num)⟩

lemma comp_bounds (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (p : Ω × Ω) : 0 ≤ comp μ f g p ∧ comp μ f g p ≤ 1 := by
  have hm : Measurable (fun z => f (p.1,z)*g (z,p.2)) := by fun_prop
  have hb := fun z => mul_unit (bf (p.1,z)) (bg (z,p.2))
  constructor
  · exact integral_nonneg (fun z => (hb z).1)
  · have h := integral_mono (unit_integrable μ _ hm hb) (integrable_const (1 : ℝ))
      (fun z => (hb z).2)
    simpa [comp] using h

/-- Composition multiplies constant row integrals, which need not be equal. -/
lemma comp_row (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (df dg : ℝ)
    (hrf : ∀ᵐ x ∂μ, ∫ y, f (x,y) ∂μ = df)
    (hrg : ∀ᵐ x ∂μ, ∫ y, g (x,y) ∂μ = dg) :
    ∀ᵐ x ∂μ, ∫ y, comp μ f g (x,y) ∂μ = df*dg := by
  filter_upwards [hrf] with x hx
  have hm : Measurable (fun p : Ω × Ω => f (x,p.1)*g p) := by fun_prop
  have hi : Integrable (fun p : Ω × Ω => f (x,p.1)*g p) (μ.prod μ) :=
    unit_integrable _ _ hm (fun p => mul_unit (bf (x,p.1)) (bg p))
  change (∫ y, ∫ z, f (x,z)*g (z,y) ∂μ ∂μ) = _
  rw [← integral_integral_swap hi]
  calc
    _ = ∫ z, f (x,z)*dg ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrg] with z hz
      rw [integral_const_mul,hz]
    _ = df*dg := by rw [integral_mul_const,hx]

/-- Reversing a composition reverses the factor order for symmetric kernels. -/
lemma comp_swap (μ : Measure Ω) (f g : Ω × Ω → ℝ)
    (hf : ∀ x y, f (x,y)=f (y,x)) (hg : ∀ x y, g (x,y)=g (y,x))
    (x y : Ω) : comp μ f g (x,y) = comp μ g f (y,x) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by dsimp only; rw [hf x z,hg z y,mul_comm])

end FourColorKernels

-- Module: FourColorKernelMatrix
open MeasureTheory
open scoped BigOperators
namespace FourColorKernelMatrix
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
noncomputable def M (W : Fin 4 → Ω × Ω → ℝ) (i j : Fin 4) (p : Ω × Ω) : ℝ :=
  (FourColorKernels.comp μ (W i) (W j) p + FourColorKernels.comp μ (W j) (W i) p)/2
lemma measurable_M (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i)) (i j : Fin 4) :
    Measurable (M (μ := μ) W i j) :=
  ((FourColorKernels.measurable_comp μ _ _ (hm i) (hm j)).add
    (FourColorKernels.measurable_comp μ _ _ (hm j) (hm i))).div_const 2
lemma M_bounds (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) (i j : Fin 4) (p : Ω × Ω) :
    0 ≤ M (μ := μ) W i j p ∧ M (μ := μ) W i j p ≤ 1 := by
  have h := FourColorKernels.comp_bounds μ _ _ (hm i) (hm j) (hb i) (hb j) p
  have k := FourColorKernels.comp_bounds μ _ _ (hm j) (hm i) (hb j) (hb i) p
  unfold M
  constructor <;> linarith
lemma M_label_symm (W : Fin 4 → Ω × Ω → ℝ) (i j : Fin 4) :
    M (μ := μ) W i j = M (μ := μ) W j i := by
  funext p; unfold M; rw [add_comm]
lemma M_row_integral (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) (d : Fin 4 → ℝ)
    (hr : ∀ i, ∀ᵐ x ∂μ, ∫ y, W i (x,y) ∂μ = d i) (i j : Fin 4) :
    ∀ᵐ x ∂μ, ∫ y, M (μ := μ) W i j (x,y) ∂μ = d i*d j := by
  have hij := FourColorKernels.comp_row μ _ _ (hm i) (hm j) (hb i) (hb j) _ _ (hr i) (hr j)
  have hji := FourColorKernels.comp_row μ _ _ (hm j) (hm i) (hb j) (hb i) _ _ (hr j) (hr i)
  filter_upwards [hij,hji] with x hx hy
  have hi := FourColorKernels.unit_integrable μ
    (fun y => FourColorKernels.comp μ (W i) (W j) (x,y))
    ((FourColorKernels.measurable_comp μ _ _ (hm i) (hm j)).comp (measurable_const.prodMk measurable_id))
    (fun y => FourColorKernels.comp_bounds μ _ _ (hm i) (hm j) (hb i) (hb j) (x,y))
  have hj := FourColorKernels.unit_integrable μ
    (fun y => FourColorKernels.comp μ (W j) (W i) (x,y))
    ((FourColorKernels.measurable_comp μ _ _ (hm j) (hm i)).comp (measurable_const.prodMk measurable_id))
    (fun y => FourColorKernels.comp_bounds μ _ _ (hm j) (hm i) (hb j) (hb i) (x,y))
  unfold M
  rw [integral_div, integral_add hi hj,hx,hy]
  ring
end FourColorKernelMatrix
namespace FourColorKernelMatrix
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma comp_sum_right (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) (i : Fin 4) (x y : Ω)
    (ht : ∀ᵐ z ∂μ, ∑ j, W j (z,y) = 1) :
    (∑ j, FourColorKernels.comp μ (W i) (W j) (x,y)) = ∫ z, W i (x,z) ∂μ := by
  have hi (j : Fin 4) : Integrable (fun z => W i (x,z)*W j (z,y)) μ :=
    FourColorKernels.unit_integrable μ _ (by fun_prop)
      (fun z => FourColorKernels.mul_unit (hb i _) (hb j _))
  unfold FourColorKernels.comp
  rw [← integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply integral_congr_ae
  filter_upwards [ht] with z hz
  rw [← Finset.mul_sum,hz,mul_one]

lemma M_marginal (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ j, W j p = 1) (d : Fin 4 → ℝ)
    (hr : ∀ i, ∀ᵐ x ∂μ, ∫ y, W i (x,y) ∂μ = d i) (i : Fin 4) :
    ∀ᵐ p ∂μ.prod μ, ∑ j, M (μ := μ) W i j p = d i := by
  have htcol : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∑ j, W j (z,y) = 1 := by
    apply (Measure.ae_ae_comm (p := fun z y => (∑ j, W j (z,y)) = 1) ?_).mp
      (Measure.ae_ae_of_ae_prod ht)
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [htcol,hr i] with x hx hix
    filter_upwards [htcol,hr i] with y hy hiy
    have ha := comp_sum_right W hm hb i x y hy
    have hb' := comp_sum_right W hm hb i y x hx
    rw [hix] at ha
    rw [hiy] at hb'
    have hc : (∑ j, FourColorKernels.comp μ (W j) (W i) (x,y)) = d i := by
      calc
        _ = ∑ j, FourColorKernels.comp μ (W i) (W j) (y,x) := by
          apply Finset.sum_congr rfl
          intro j _
          exact FourColorKernels.comp_swap μ _ _ (hs j) (hs i) x y
        _ = d i := hb'
    change (∑ j, (FourColorKernels.comp μ (W i) (W j) (x,y) +
      FourColorKernels.comp μ (W j) (W i) (x,y))/2) = d i
    rw [← Finset.sum_div,Finset.sum_add_distrib,ha,hc]
    ring
  · apply measurableSet_eq_fun _ measurable_const
    exact Finset.measurable_sum _ (fun j _ => measurable_M W hm i j)
end FourColorKernelMatrix

-- Module: FourColorRepresentatives
open MeasureTheory

namespace Submissions.E811FourColorParity.Representatives
noncomputable def clip {α : Type*} (f : α → ℝ) (p : α) : ℝ := max 0 (min 1 (f p))
noncomputable def symclip {Ω : Type*} (f : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  (clip f p + clip f (p.2,p.1))/2

lemma clip_bounds {α : Type*} (f : α → ℝ) (p : α) :
    0 ≤ clip f p ∧ clip f p ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma symclip_bounds {Ω : Type*} (f : Ω × Ω → ℝ) (p : Ω × Ω) :
    0 ≤ symclip f p ∧ symclip f p ≤ 1 := by
  have h := clip_bounds f p
  have h' := clip_bounds f (p.2,p.1)
  unfold symclip
  constructor <;> linarith

lemma symclip_symm {Ω : Type*} (f : Ω × Ω → ℝ) (p : Ω × Ω) :
    symclip f p = symclip f (p.2,p.1) := by simp [symclip,add_comm]

lemma measurable_symclip {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω × Ω → ℝ} (hf : Measurable f) : Measurable (symclip f) := by
  have hc : Measurable (clip f) := measurable_const.max (measurable_const.min hf)
  exact (hc.add (hc.comp measurable_swap)).div_const 2

lemma symclip_eq_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (f : Ω × Ω → ℝ)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ f p ∧ f p ≤ 1)
    (hs : ∀ᵐ p ∂μ.prod μ, f p = f (p.2,p.1)) :
    symclip f =ᵐ[μ.prod μ] f := by
  filter_upwards [hb,hs] with p hp hs
  unfold symclip clip
  rw [← hs]
  simp only [min_eq_right hp.2,max_eq_right hp.1]
  ring

noncomputable def cycle4 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g h k : Ω × Ω → ℝ) : ℝ :=
  ∫ x, ∫ y, ∫ z, ∫ t, f (x,y) * g (y,z) * h (z,t) * k (t,x) ∂μ ∂μ ∂μ ∂μ

lemma cycle4_congr {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {f f' g g' h h' k k' : Ω × Ω → ℝ}
    (hf : f =ᵐ[μ.prod μ] f') (hg : g =ᵐ[μ.prod μ] g')
    (hh : h =ᵐ[μ.prod μ] h') (hk : k =ᵐ[μ.prod μ] k') :
    cycle4 μ f g h k = cycle4 μ f' g' h' k' := by
  have hk' := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq hk)
  unfold cycle4
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hf,hk'] with x hfx hkx
  apply integral_congr_ae
  filter_upwards [hfx,Measure.ae_ae_of_ae_prod hg] with y hfy hgy
  apply integral_congr_ae
  filter_upwards [hgy,Measure.ae_ae_of_ae_prod hh] with z hgz hhz
  apply integral_congr_ae
  filter_upwards [hhz,hkx] with t hht hkt
  change k (t,x) = k' (t,x) at hkt
  rw [hfy,hgz,hht,hkt]

end Submissions.E811FourColorParity.Representatives

-- Module: FourColorCycleMatrix
open MeasureTheory
namespace FourColorCycleMatrix
open FourColorKernels
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

@[fun_prop] lemma measurable_integrate {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) [SFinite ν] (f : A → B → ℝ) (hf : Measurable (Function.uncurry f)) :
    Measurable (fun a => ∫ b, f a b ∂ν) :=
  hf.stronglyMeasurable.integral_prod_right.measurable

lemma integral_unit_bounds (f : Ω → ℝ) (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∫ x, f x ∂μ) ∧ (∫ x, f x ∂μ) ≤ 1 := by
  constructor
  · exact integral_nonneg (fun x => (hb x).1)
  · simpa using integral_mono (unit_integrable μ f hf hb) (integrable_const (1 : ℝ))
      (fun x => (hb x).2)

lemma comp_pair_cycle (f g h k : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) (bk : ∀ p, 0 ≤ k p ∧ k p ≤ 1)
    (sh : ∀ x y, h (x,y)=h (y,x)) (sk : ∀ x y, k (x,y)=k (y,x)) :
    (∫ p, comp μ f g p * comp μ h k p ∂μ.prod μ) = cycle4 μ f g k h := by
  have hm : Measurable (fun p => comp μ f g p * comp μ h k p) :=
    (measurable_comp μ f g hf hg).mul (measurable_comp μ h k hh hk)
  have hb := fun p => mul_unit (comp_bounds μ f g hf hg bf bg p) (comp_bounds μ h k hh hk bh bk p)
  rw [integral_prod _ (unit_integrable _ _ hm hb)]
  simp_rw [comp, ← integral_mul_const, ← integral_const_mul]
  unfold cycle4
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hi : Integrable (fun p : Ω × Ω => ∫ t,
      (f (x,p.2)*g (p.2,p.1))*(h (x,t)*k (t,p.1)) ∂μ) (μ.prod μ) := by
    apply unit_integrable _ _ (by fun_prop)
    intro p
    apply integral_unit_bounds _ (by fun_prop)
    intro t
    exact mul_unit (mul_unit (bf _) (bg _)) (mul_unit (bh _) (bk _))
  dsimp only
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [sh x t,sk t z]
  ring

lemma comp_pair_zero_ae (f g h k : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) (bk : ∀ p, 0 ≤ k p ∧ k p ≤ 1)
    (sh : ∀ x y, h (x,y)=h (y,x)) (sk : ∀ x y, k (x,y)=k (y,x))
    (hz : cycle4 μ f g k h = 0) :
    ∀ᵐ p ∂μ.prod μ, comp μ f g p * comp μ h k p = 0 := by
  have hm : Measurable (fun p => comp μ f g p * comp μ h k p) :=
    (measurable_comp μ f g hf hg).mul (measurable_comp μ h k hh hk)
  have hb := fun p => mul_unit (comp_bounds μ f g hf hg bf bg p) (comp_bounds μ h k hh hk bh bk p)
  have hi := unit_integrable (μ.prod μ) _ hm hb
  have hz' := (comp_pair_cycle f g h k hf hg hh hk bf bg bh bk sh sk).trans hz
  exact (integral_eq_zero_iff_of_nonneg (fun p => (hb p).1) hi).mp hz'
end FourColorCycleMatrix
namespace FourColorCycleMatrix
open FourColorKernels
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma M_pair_zero_ae (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x)) (i j k l : Fin 4)
    (h0 : cycle4 μ (W i) (W j) (W l) (W k)=0)
    (h1 : cycle4 μ (W i) (W j) (W k) (W l)=0)
    (h2 : cycle4 μ (W j) (W i) (W l) (W k)=0)
    (h3 : cycle4 μ (W j) (W i) (W k) (W l)=0) :
    ∀ᵐ p ∂μ.prod μ,
      FourColorKernelMatrix.M (μ := μ) W i j p * FourColorKernelMatrix.M (μ := μ) W k l p = 0 := by
  have e0 := comp_pair_zero_ae (W i) (W j) (W k) (W l)
    (hm i) (hm j) (hm k) (hm l) (hb i) (hb j) (hb k) (hb l) (hs k) (hs l) h0
  have e1 := comp_pair_zero_ae (W i) (W j) (W l) (W k)
    (hm i) (hm j) (hm l) (hm k) (hb i) (hb j) (hb l) (hb k) (hs l) (hs k) h1
  have e2 := comp_pair_zero_ae (W j) (W i) (W k) (W l)
    (hm j) (hm i) (hm k) (hm l) (hb j) (hb i) (hb k) (hb l) (hs k) (hs l) h2
  have e3 := comp_pair_zero_ae (W j) (W i) (W l) (W k)
    (hm j) (hm i) (hm l) (hm k) (hb j) (hb i) (hb l) (hb k) (hs l) (hs k) h3
  filter_upwards [e0,e1,e2,e3] with p hp0 hp1 hp2 hp3
  unfold FourColorKernelMatrix.M
  nlinarith
end FourColorCycleMatrix

namespace FourColorCycleMatrix
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma complementary_M_products_zero (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (hcycle : ∀ σ : Equiv.Perm (Fin 4), cycle4 μ (W (σ 0)) (W (σ 1)) (W (σ 2)) (W (σ 3))=0) :
    ∀ᵐ p ∂μ.prod μ,
      FourColorKernelMatrix.M (μ := μ) W 0 1 p * FourColorKernelMatrix.M (μ := μ) W 2 3 p = 0 ∧
      FourColorKernelMatrix.M (μ := μ) W 0 2 p * FourColorKernelMatrix.M (μ := μ) W 1 3 p = 0 ∧
      FourColorKernelMatrix.M (μ := μ) W 0 3 p * FourColorKernelMatrix.M (μ := μ) W 1 2 p = 0 := by
  have hz (a b c d : Fin 4) (h : Function.Bijective ![a,b,c,d]) :
      cycle4 μ (W a) (W b) (W c) (W d)=0 := by
    exact hcycle (Equiv.ofBijective ![a,b,c,d] h)
  have h0 := M_pair_zero_ae W hm hb hs 0 1 2 3
    (hz 0 1 3 2 (by decide))
    (hz 0 1 2 3 (by decide))
    (hz 1 0 3 2 (by decide))
    (hz 1 0 2 3 (by decide))
  have h1 := M_pair_zero_ae W hm hb hs 0 2 1 3
    (hz 0 2 3 1 (by decide))
    (hz 0 2 1 3 (by decide))
    (hz 2 0 3 1 (by decide))
    (hz 2 0 1 3 (by decide))
  have h2 := M_pair_zero_ae W hm hb hs 0 3 1 2
    (hz 0 3 2 1 (by decide))
    (hz 0 3 1 2 (by decide))
    (hz 3 0 2 1 (by decide))
    (hz 3 0 1 2 (by decide))
  filter_upwards [h0,h1,h2] with p hp0 hp1 hp2
  exact ⟨hp0,hp1,hp2⟩
end FourColorCycleMatrix

-- Module: FourColorTransport

namespace Submissions.E811FourColorParity.Transport

/-- Local transport inequality, with equality rigid away from saturation.
The three zero products are precisely complementary-pair rainbow exclusion. -/
theorem gap (a b c d x y z u v w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (r0 : a + x + y + z = 1/2)
    (r1 : b + x + u + v = 1/6)
    (r2 : c + y + u + w = 1/6)
    (r3 : d + z + v + w = 1/6)
    (ex : x * w = 0) (ey : y * v = 0) (ez : z * u = 0)
    (hunsat : a < 1/2) :
    0 ≤ 3*(b+c+d)-a ∧ (3*(b+c+d)-a = 0 → a = 0) := by
  rcases mul_eq_zero.mp ex with hx0 | hw0 <;>
  rcases mul_eq_zero.mp ey with hy0 | hv0 <;>
  rcases mul_eq_zero.mp ez with hz0 | hu0 <;>
  constructor <;> (first | intro heq | skip) <;> linarith

theorem matrix_gap (M : Fin 4 → Fin 4 → ℝ)
    (hn : ∀ i j, 0 ≤ M i j) (hs : ∀ i j, M i j = M j i)
    (hr : ∀ i, ∑ j, M i j = if i = 0 then 1/2 else 1/6)
    (h1 : M 0 1 * M 2 3 = 0)
    (h2 : M 0 2 * M 1 3 = 0)
    (h3 : M 0 3 * M 1 2 = 0)
    (ha : M 0 0 < 1/2) :
    0 ≤ 3*(M 1 1+M 2 2+M 3 3)-M 0 0 ∧
      (3*(M 1 1+M 2 2+M 3 3)-M 0 0 = 0 → M 0 0 = 0) := by
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have r3 := hr 3
  norm_num [Fin.sum_univ_succ] at r0 r1 r2 r3
  change M 0 0 + (M 0 1 + (M 0 2 + M 0 3)) = 1/2 at r0
  change M 1 0 + (M 1 1 + (M 1 2 + M 1 3)) = 1/6 at r1
  change M 2 0 + (M 2 1 + (M 2 2 + M 2 3)) = 1/6 at r2
  change M 3 0 + (M 3 1 + (M 3 2 + M 3 3)) = 1/6 at r3
  rw [hs 1 0] at r1
  rw [hs 2 0, hs 2 1] at r2
  rw [hs 3 0, hs 3 1, hs 3 2] at r3
  exact gap _ _ _ _ _ _ _ _ _ _ (hn 0 0) (hn 1 1) (hn 2 2) (hn 3 3)
    (hn 0 1) (hn 0 2) (hn 0 3) (hn 1 2) (hn 1 3) (hn 2 3)
    (by linarith) (by linarith) (by linarith) (by linarith) h1 h2 h3 ha

end Submissions.E811FourColorParity.Transport

-- Module: FourColorSaturation

open MeasureTheory

namespace Submissions.E811FourColorParity.Saturation

/-- The local gap rule and exact row moments force a saturated fiber. -/
theorem not_ae_unsaturated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a s : Ω → ℝ)
    (ha : Integrable a μ) (hs : Integrable s μ)
    (hIa : ∫ x, a x ∂μ = 1/4) (hIs : ∫ x, s x ∂μ = 1/12)
    (hgap : ∀ᵐ x ∂μ, a x < 1/2 →
      0 ≤ 3*s x-a x ∧ (3*s x-a x = 0 → a x = 0)) :
    ¬ (∀ᵐ x ∂μ, a x < 1/2) := by
  intro hsmall
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ 3*s x-a x := by
    filter_upwards [hgap, hsmall] with x hg hx
    exact (hg hx).1
  have hi : Integrable (fun x => 3*s x-a x) μ := (hs.const_mul 3).sub ha
  have hz : (∫ x, 3*s x-a x ∂μ) = 0 := by
    rw [integral_sub (hs.const_mul 3) ha, integral_const_mul, hIa, hIs]
    norm_num
  have hz_ae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hz
  have ha_ae : a =ᵐ[μ] 0 := by
    filter_upwards [hgap,hsmall,hz_ae] with x hg hx hz
    exact (hg hx).2 hz
  have : (∫ x, a x ∂μ) = 0 := by
    calc
      (∫ x, a x ∂μ) = ∫ x, (0 : ℝ) ∂μ := integral_congr_ae ha_ae
      _ = 0 := integral_zero _ _
  linarith

theorem saturation_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a s : Ω → ℝ)
    (ha : Integrable a μ) (hs : Integrable s μ)
    (hIa : ∫ x, a x ∂μ = 1/4) (hIs : ∫ x, s x ∂μ = 1/12)
    (hbound : ∀ᵐ x ∂μ, a x ≤ 1/2)
    (hgap : ∀ᵐ x ∂μ, a x < 1/2 →
      0 ≤ 3*s x-a x ∧ (3*s x-a x = 0 → a x = 0)) :
    0 < μ {x | a x = 1/2} := by
  by_contra hp
  have hz : μ {x | a x = 1/2} = 0 := le_antisymm (le_of_not_gt hp) bot_le
  have hne : ∀ᵐ x ∂μ, a x ≠ (1/2 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using hz
  apply not_ae_unsaturated μ a s ha hs hIa hIs hgap
  filter_upwards [hbound,hne] with x hx hn
  exact lt_of_le_of_ne hx hn

end Submissions.E811FourColorParity.Saturation

-- Module: FourColorSaturationBridge
open MeasureTheory
namespace FourColorSaturationBridge
open FourColorKernelMatrix
variable {Ω : Type*} [MeasurableSpace Ω]

theorem positive_saturation_fibers (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ j, W j p = 1)
    (hr : ∀ i, ∀ᵐ x ∂μ, ∫ y, W i (x,y) ∂μ = if i=0 then (1:ℝ)/2 else 1/6)
    (hz : ∀ᵐ p ∂μ.prod μ,
      M (μ := μ) W 0 1 p * M (μ := μ) W 2 3 p = 0 ∧
      M (μ := μ) W 0 2 p * M (μ := μ) W 1 3 p = 0 ∧
      M (μ := μ) W 0 3 p * M (μ := μ) W 1 2 p = 0) :
    ∀ᵐ x ∂μ, 0 < μ {y | FourColorKernels.comp μ (W 0) (W 0) (x,y) = (1:ℝ)/2} := by
  let d : Fin 4 → ℝ := fun i => if i=0 then 1/2 else 1/6
  have hmar := (ae_all_iff).mpr (fun i => M_marginal (μ := μ) W hm hb hs ht d hr i)
  have hloc : ∀ᵐ p ∂μ.prod μ,
      M (μ := μ) W 0 0 p ≤ 1/2 ∧
      (M (μ := μ) W 0 0 p < 1/2 →
        0 ≤ 3*(M (μ := μ) W 1 1 p+M (μ := μ) W 2 2 p+M (μ := μ) W 3 3 p)-M (μ := μ) W 0 0 p ∧
        (3*(M (μ := μ) W 1 1 p+M (μ := μ) W 2 2 p+M (μ := μ) W 3 3 p)-M (μ := μ) W 0 0 p=0 → M (μ := μ) W 0 0 p=0)) := by
    filter_upwards [hmar,hz] with p hp hzp
    have hnon i j := (M_bounds (μ := μ) W hm hb i j p).1
    constructor
    · have h0 := hp 0
      norm_num [d,Fin.sum_univ_succ] at h0
      change M (μ := μ) W 0 0 p + (M (μ := μ) W 0 1 p + (M (μ := μ) W 0 2 p + M (μ := μ) W 0 3 p)) = 1/2 at h0
      linarith [hnon 0 1,hnon 0 2,hnon 0 3]
    · exact Submissions.E811FourColorParity.Transport.matrix_gap
        (fun i j => M (μ := μ) W i j p) hnon
        (fun i j => congrFun (M_label_symm (μ := μ) W i j) p)
        hp hzp.1 hzp.2.1 hzp.2.2
  have h0 := M_row_integral (μ := μ) W hm hb d hr 0 0
  have h1 := M_row_integral (μ := μ) W hm hb d hr 1 1
  have h2 := M_row_integral (μ := μ) W hm hb d hr 2 2
  have h3 := M_row_integral (μ := μ) W hm hb d hr 3 3
  filter_upwards [h0,h1,h2,h3,Measure.ae_ae_of_ae_prod hloc] with x hx0 hx1 hx2 hx3 hx
  have hi (i : Fin 4) : Integrable (fun y => M (μ := μ) W i i (x,y)) μ :=
    FourColorKernels.unit_integrable μ _
      ((measurable_M (μ := μ) W hm i i).comp (measurable_const.prodMk measurable_id))
      (fun y => M_bounds (μ := μ) W hm hb i i (x,y))
  have ha : ∫ y, M (μ := μ) W 0 0 (x,y) ∂μ = (1:ℝ)/4 := by norm_num [d] at hx0 ⊢; exact hx0
  have hsmall : ∫ y, (M (μ := μ) W 1 1 (x,y)+M (μ := μ) W 2 2 (x,y)+M (μ := μ) W 3 3 (x,y)) ∂μ = (1:ℝ)/12 := by
    rw [integral_add (f := fun y => M (μ := μ) W 1 1 (x,y)+M (μ := μ) W 2 2 (x,y)) (g := fun y => M (μ := μ) W 3 3 (x,y)) ((hi 1).add (hi 2)) (hi 3), integral_add (hi 1) (hi 2),hx1,hx2,hx3]
    norm_num [d, show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]
  have hp := Submissions.E811FourColorParity.Saturation.saturation_positive μ
    (fun y => M (μ := μ) W 0 0 (x,y))
    (fun y => M (μ := μ) W 1 1 (x,y)+M (μ := μ) W 2 2 (x,y)+M (μ := μ) W 3 3 (x,y))
    (hi 0) (((hi 1).add (hi 2)).add (hi 3)) ha hsmall
    (hx.mono (fun _ h => h.1)) (hx.mono (fun _ h => h.2))
  simpa only [M,add_self_div_two] using hp

end FourColorSaturationBridge

-- Module: FourColorEqualRows
open MeasureTheory
namespace FourColorEqualRows
variable {Ω : Type*} [MeasurableSpace Ω]

lemma unit_integrable (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  filter_upwards [hb] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- Equal mass and maximal overlap force two unit-bounded functions to be the same indicator. -/
lemma equal_indicator_of_saturated_overlap (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (bg : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1)
    (q : ℝ) (hfi : ∫ x, f x ∂μ = q) (hgi : ∫ x, g x ∂μ = q)
    (hfg : ∫ x, f x*g x ∂μ = q) :
    ∀ᵐ x ∂μ, f x = g x ∧ (f x = 0 ∨ f x = 1) := by
  have hi := unit_integrable μ f hf bf
  have hj := unit_integrable μ g hg bg
  have hprod : Integrable (fun x => f x*g x) μ := by
    apply unit_integrable μ _ (hf.mul hg)
    filter_upwards [bf,bg] with x hx hy
    exact ⟨mul_nonneg hx.1 hy.1, (mul_le_mul hx.2 hy.2 hy.1 (by norm_num)).trans_eq (by norm_num)⟩
  have hn1 : ∀ᵐ x ∂μ, 0 ≤ f x-f x*g x := by
    filter_upwards [bf,bg] with x hx hy
    nlinarith
  have hn2 : ∀ᵐ x ∂μ, 0 ≤ g x-f x*g x := by
    filter_upwards [bf,bg] with x hx hy
    nlinarith
  have hz1 : ∫ x, f x-f x*g x ∂μ = 0 := by
    rw [integral_sub hi hprod,hfi,hfg]; ring
  have hz2 : ∫ x, g x-f x*g x ∂μ = 0 := by
    rw [integral_sub hj hprod,hgi,hfg]; ring
  have ha := (integral_eq_zero_iff_of_nonneg_ae hn1 (hi.sub hprod)).mp hz1
  have hb := (integral_eq_zero_iff_of_nonneg_ae hn2 (hj.sub hprod)).mp hz2
  filter_upwards [ha,hb] with x hx hy
  change f x-f x*g x=0 at hx
  change g x-f x*g x=0 at hy
  have he : f x = g x := by linarith
  refine ⟨he, ?_⟩
  have hp : f x*(f x-1)=0 := by rw [← he] at hx; nlinarith
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

lemma half_rows_equal_indicator (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (bg : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1)
    (hfi : ∫ x, f x ∂μ = (1:ℝ)/2) (hgi : ∫ x, g x ∂μ = (1:ℝ)/2)
    (hfg : ∫ x, f x*g x ∂μ = (1:ℝ)/2) :
    ∀ᵐ x ∂μ, f x = g x ∧ (f x = 0 ∨ f x = 1) :=
  equal_indicator_of_saturated_overlap μ f g hf hg bf bg _ hfi hgi hfg

end FourColorEqualRows

-- Module: FourColorRowDistance
open MeasureTheory
namespace FourColorRowDistance
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def rowDist (A : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  ∫ z, |A (p.1,z)-A (p.2,z)| ∂μ

theorem measurable_rowDist (A : Ω × Ω → ℝ) (hm : Measurable A) :
    Measurable (rowDist μ A) := by
  have h : Measurable (fun p : (Ω × Ω) × Ω => |A (p.1.1,p.2)-A (p.1.2,p.2)|) := by fun_prop
  exact h.stronglyMeasurable.integral_prod_right.measurable

theorem rowDist_eq_zero_iff (A : Ω × Ω → ℝ) (hm : Measurable A)
    (hb : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (x y : Ω) :
    rowDist μ A (x,y) = 0 ↔ (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z)) := by
  have hi : Integrable (fun z => |A (x,z)-A (y,z)|) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_le.mpr ⟨by linarith [(hb (x,z)).1,(hb (y,z)).2],
      by linarith [(hb (x,z)).2,(hb (y,z)).1]⟩
  rw [rowDist, integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z => abs_nonneg (A (x,z)-A (y,z)))) hi]
  constructor
  · intro h
    filter_upwards [h] with z hz
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  · intro h
    filter_upwards [h] with z hz
    simp [hz]

theorem measurable_twin_class (A : Ω × Ω → ℝ) (hm : Measurable A)
    (hb : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (x : Ω) :
    MeasurableSet {y | (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z))} := by
  have he : {y | (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z))} =
      {y | rowDist μ A (x,y) = 0} := by
    ext y
    exact (rowDist_eq_zero_iff μ A hm hb x y).symm
  rw [he]
  exact measurableSet_eq_fun ((measurable_rowDist μ A hm).comp (measurable_const.prodMk measurable_id)) measurable_const

omit [IsProbabilityMeasure μ] in
theorem twin_equivalence (A : Ω × Ω → ℝ) :
    Equivalence (fun x y => (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z))) := by
  refine ⟨fun x => Filter.EventuallyEq.rfl, ?_, ?_⟩
  · intro x y h
    exact h.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

end FourColorRowDistance

-- Module: FourColorTwinExtraction
open MeasureTheory
namespace FourColorTwinExtraction
variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_good_subset (μ : Measure Ω) (P : Ω → Prop)
    (hp : ∀ᵐ x ∂μ, P x) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ x ∂μ, x ∈ G) ∧ ∀ x ∈ G, P x := by
  have hn : μ {x | ¬ P x} = 0 := by simpa only [ae_iff] using hp
  obtain ⟨N,hsub,hm,hN⟩ := exists_measurable_superset_of_null hn
  refine ⟨Nᶜ,hm.compl,?_,?_⟩
  · exact (measure_eq_zero_iff_ae_notMem).mp hN
  · intro x hx
    by_contra h
    exact hx (hsub h)

theorem extract_twins (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω × Ω → ℝ) (hm : Measurable A)
    (hb : ∀ p, 0 ≤ A p ∧ A p ≤ 1)
    (hs : ∀ x y, A (x,y) = A (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y, A (x,y) ∂μ = (1:ℝ)/2)
    (hp : ∀ᵐ x ∂μ, 0 < μ {y | FourColorKernels.comp μ A A (x,y) = (1:ℝ)/2}) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ x ∂μ, x ∈ G) ∧
      ∀ x ∈ G,
        (∫ y, A (x,y) ∂μ = (1:ℝ)/2) ∧
        (∀ᵐ z ∂μ, A (x,z) = 0 ∨ A (x,z) = 1) ∧
        0 < μ {y | y ∈ G ∧ (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z))} := by
  obtain ⟨G,hG,hGa,hgood⟩ := measurable_good_subset μ
    (fun x => (∫ y, A (x,y) ∂μ = (1:ℝ)/2) ∧
      0 < μ {y | FourColorKernels.comp μ A A (x,y) = (1:ℝ)/2}) (hr.and hp)
  have heq (x : Ω) (hx : x ∈ G) (y : Ω) (hy : y ∈ G)
      (hxy : FourColorKernels.comp μ A A (x,y) = (1:ℝ)/2) :
      ∀ᵐ z ∂μ, A (x,z) = A (y,z) ∧ (A (x,z) = 0 ∨ A (x,z) = 1) := by
    apply FourColorEqualRows.half_rows_equal_indicator μ
      (fun z => A (x,z)) (fun z => A (y,z)) (by fun_prop) (by fun_prop)
      (Filter.Eventually.of_forall (fun z => hb (x,z)))
      (Filter.Eventually.of_forall (fun z => hb (y,z)))
      (hgood x hx).1 (hgood y hy).1
    simpa only [FourColorKernels.comp,hs] using hxy
  refine ⟨G,hG,hGa,?_⟩
  intro x hx
  have hf := (frequently_ae_iff.mpr (ne_of_gt (hgood x hx).2)).and_eventually hGa
  obtain ⟨y,hxy,hy⟩ := hf.exists
  refine ⟨(hgood x hx).1,(heq x hx y hy hxy).mono (fun _ h => h.2),?_⟩
  apply lt_of_le_of_ne zero_le
  intro hz
  have hfreq : ∃ᶠ y in ae μ, y ∈ G ∧
      (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z)) := by
    apply hf.mono
    intro y h
    exact ⟨h.2,(heq x hx y h.2 h.1).mono (fun _ hh => hh.1)⟩
  exact (frequently_ae_iff.mp hfreq) hz.symm

end FourColorTwinExtraction

-- Module: FourColorBlock

open MeasureTheory
open scoped BigOperators
namespace FourColorBlock

/-- The sum of three real squares dominates one third of the squared sum. -/
lemma three_square_sum (a b c : ℝ) :
    (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

lemma fin_three_square_sum (a : Fin 3 → ℝ) :
    (∑ i, a i)^2 ≤ 3 * ∑ i, (a i)^2 := by
  simpa [Fin.sum_univ_succ, add_assoc] using three_square_sum (a 0) (a 1) (a 2)

/-- No finite-mass assumption is needed: integrability of the three squares suffices. -/
lemma integral_three_square_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Fin 3 → Ω → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hsq : ∀ i, Integrable (fun x => (f i x)^2) μ) :
    (∫ x, (∑ i, f i x)^2 ∂μ) ≤ 3 * ∫ x, ∑ i, (f i x)^2 ∂μ := by
  have hi : Integrable (fun x => ∑ i, (f i x)^2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hsq i)
  have hj : Integrable (fun x => (∑ i, f i x)^2) μ := by
    apply (hi.const_mul 3).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact fin_three_square_sum (fun i => f i x)
  calc
    _ ≤ ∫ x, 3 * ∑ i, (f i x)^2 ∂μ :=
      integral_mono hj (hi.const_mul 3) (fun x => fin_three_square_sum (fun i => f i x))
    _ = _ := integral_const_mul _ _

/-- If the block sum has fixed integral, the same inequality gives compensation. -/
lemma integral_block_compensation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Fin 3 → Ω → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hsq : ∀ i, Integrable (fun x => (f i x)^2) μ)
    (q : ℝ) (hq : q ≤ ∫ x, (∑ i, f i x)^2 ∂μ) :
    q ≤ 3 * ∫ x, ∑ i, (f i x)^2 ∂μ :=
  hq.trans (integral_three_square_sum μ f hf hsq)

end FourColorBlock

-- Module: FourColorTwinBlock
open MeasureTheory
open scoped BigOperators
namespace FourColorTwinBlock
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def flux (ν : Measure Ω) (W : Ω × Ω → ℝ) (z : Ω) : ℝ := ∫ x, W (x,z) ∂ν

lemma block_energy (X : Set Ω) (W : Ω × Ω → ℝ) (hW : Measurable W)
    (hb : ∀ p, 0 ≤ W p ∧ W p ≤ 1) (hs : ∀ x y, W (x,y)=W (y,x)) :
    (∫ p, FourColorKernels.comp μ W W p ∂(μ.restrict X).prod (μ.restrict X)) =
      ∫ z, (flux (μ.restrict X) W z)^2 ∂μ := by
  let ν := μ.restrict X
  have hm : Measurable (fun p : (Ω × Ω) × Ω => W (p.1.1,p.2)*W (p.2,p.1.2)) := by fun_prop
  have hi : Integrable (fun p : (Ω × Ω) × Ω => W (p.1.1,p.2)*W (p.2,p.1.2)) ((ν.prod ν).prod μ) :=
    FourColorKernels.unit_integrable _ _ hm
      (fun p => FourColorKernels.mul_unit (hb _) (hb _))
  unfold FourColorKernels.comp
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have he : (fun p : Ω × Ω => W (p.1,z)*W (z,p.2)) =
      (fun p => W (p.1,z)*W (p.2,z)) := by funext p; rw [hs z p.2]
  change (∫ p, W (p.1,z)*W (z,p.2) ∂ν.prod ν) = _
  rw [he]
  simpa [flux,pow_two] using (integral_prod_mul (μ := ν) (ν := ν) (fun x => W (x,z)) (fun y => W (y,z)))

/-- The three light-color fluxes compensate the heavy flux whenever their squared total
has at least the heavy squared mass. This is the integrated block step. -/
lemma compensation_from_flux (X : Set Ω) (W : Fin 4 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (hflux : (∫ z, (flux (μ.restrict X) (W 0) z)^2 ∂μ) ≤
      ∫ z, (∑ i : Fin 3, flux (μ.restrict X) (W i.succ) z)^2 ∂μ)
    (hfi : ∀ i : Fin 3, Integrable (fun z => (flux (μ.restrict X) (W i.succ) z)^2) μ) :
    (∫ p, FourColorKernels.comp μ (W 0) (W 0) p ∂(μ.restrict X).prod (μ.restrict X)) ≤
      3 * ∑ i : Fin 3, ∫ p, FourColorKernels.comp μ (W i.succ) (W i.succ) p ∂(μ.restrict X).prod (μ.restrict X) := by
  have hfm (i : Fin 3) : Measurable (flux (μ.restrict X) (W i.succ)) :=
    (hW i.succ).stronglyMeasurable.integral_prod_left'.measurable
  have h := FourColorBlock.integral_three_square_sum μ
    (fun i z => flux (μ.restrict X) (W i.succ) z) hfm hfi
  rw [integral_finsetSum _ (fun i _ => hfi i)] at h
  rw [block_energy X (W 0) (hW 0) (hb 0) (hs 0)]
  have he : (∑ i : Fin 3, ∫ p, FourColorKernels.comp μ (W i.succ) (W i.succ) p ∂(μ.restrict X).prod (μ.restrict X)) =
      ∑ i : Fin 3, ∫ z, (flux (μ.restrict X) (W i.succ) z)^2 ∂μ := by
    apply Finset.sum_congr rfl
    intro i _
    exact block_energy X _ (hW _) (hb _) (hs _)
  rw [he]
  exact hflux.trans h
end FourColorTwinBlock
namespace FourColorTwinBlock
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma flux_square_integrable (X : Set Ω) (W : Ω × Ω → ℝ) (hW : Measurable W)
    (hb : ∀ p, 0 ≤ W p ∧ W p ≤ 1) : Integrable (fun z => (flux (μ.restrict X) W z)^2) μ := by
  let t := (μ.restrict X).real Set.univ
  have ht : 0 ≤ t := measureReal_nonneg
  have hbound (z : Ω) : 0 ≤ flux (μ.restrict X) W z ∧ flux (μ.restrict X) W z ≤ t := by
    constructor
    · exact integral_nonneg (fun x => (hb (x,z)).1)
    · have hi := FourColorKernels.unit_integrable (μ.restrict X) (fun x => W (x,z))
        (hW.comp (measurable_id.prodMk measurable_const)) (fun x => hb (x,z))
      have h := integral_mono hi (integrable_const (1 : ℝ)) (fun x => (hb (x,z)).2)
      simpa [flux,t] using h
  apply Integrable.of_bound ((hW.stronglyMeasurable.integral_prod_left'.measurable).pow_const 2).aestronglyMeasurable (t^2)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (hbound z).1 (hbound z).2 2

lemma indicator_flux_compensation (X : Set Ω) (W : Fin 4 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x)) (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ᵐ z ∂μ, f z=0 ∨ f z=1) (hfi : ∫ z, f z ∂μ = (1:ℝ)/2)
    (t : ℝ)
    (h0 : ∀ᵐ z ∂μ, flux (μ.restrict X) (W 0) z=t*f z)
    (hl : ∀ᵐ z ∂μ, ∑ i : Fin 3, flux (μ.restrict X) (W i.succ) z=t*(1-f z)) :
    (∫ p, FourColorKernels.comp μ (W 0) (W 0) p ∂(μ.restrict X).prod (μ.restrict X)) ≤
      3 * ∑ i : Fin 3, ∫ p, FourColorKernels.comp μ (W i.succ) (W i.succ) p ∂(μ.restrict X).prod (μ.restrict X) := by
  have hi : Integrable f μ := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards [bf] with z hz
    rcases hz with hz | hz <;> simp [hz]
  have e0 : (∫ z, (flux (μ.restrict X) (W 0) z)^2 ∂μ) = t^2/2 := by
    calc
      _ = ∫ z, t^2*f z ∂μ := by
        apply integral_congr_ae
        filter_upwards [h0,bf] with z hz hfz
        rcases hfz with hfz | hfz <;> simp [hz,hfz]
      _ = _ := by rw [integral_const_mul,hfi]; ring
  have el : (∫ z, (∑ i : Fin 3, flux (μ.restrict X) (W i.succ) z)^2 ∂μ) = t^2/2 := by
    calc
      _ = ∫ z, t^2*(1-f z) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hl,bf] with z hz hfz
        rcases hfz with hfz | hfz <;> simp [hz,hfz]
      _ = _ := by rw [integral_const_mul,integral_sub (integrable_const _) hi,hfi]; simp; ring
  apply compensation_from_flux X W hW hb hs
  · rw [e0,el]
  · exact fun i => flux_square_integrable X _ (hW _) (hb _)
end FourColorTwinBlock
namespace FourColorTwinBlock
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
lemma twin_block_compensation (X : Set Ω) (W : Fin 4 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (htotal : ∀ᵐ p ∂μ.prod μ, ∑ i, W i p=1)
    (f : Ω → ℝ) (hf : Measurable f) (bf : ∀ᵐ z ∂μ, f z=0 ∨ f z=1)
    (hfi : ∫ z, f z ∂μ = (1:ℝ)/2)
    (htwin : ∀ᵐ x ∂μ.restrict X, ∀ᵐ z ∂μ, W 0 (x,z)=f z) :
    (∫ p, FourColorKernels.comp μ (W 0) (W 0) p ∂(μ.restrict X).prod (μ.restrict X)) ≤
      3 * ∑ i : Fin 3, ∫ p, FourColorKernels.comp μ (W i.succ) (W i.succ) p ∂(μ.restrict X).prod (μ.restrict X) := by
  let t := (μ.restrict X).real Set.univ
  have htr : ∀ᵐ z ∂μ, ∀ᵐ x ∂μ.restrict X, W 0 (x,z)=f z := by
    apply (Measure.ae_ae_comm (p := fun x z => W 0 (x,z)=f z) ?_).mp htwin
    exact measurableSet_eq_fun (hW 0) (hf.comp measurable_snd)
  have h0 : ∀ᵐ z ∂μ, flux (μ.restrict X) (W 0) z=t*f z := by
    filter_upwards [htr] with z hz
    unfold flux
    rw [integral_congr_ae hz]
    simp [t]
  have hcol : ∀ᵐ z ∂μ, ∀ᵐ x ∂μ, ∑ i, W i (x,z)=1 := by
    apply (Measure.ae_ae_comm (p := fun x z => (∑ i, W i (x,z))=1) ?_).mp
      (Measure.ae_ae_of_ae_prod htotal)
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hsum : ∀ᵐ z ∂μ, ∑ i, flux (μ.restrict X) (W i) z=t := by
    filter_upwards [hcol] with z hz
    have hi (i : Fin 4) : Integrable (fun x => W i (x,z)) (μ.restrict X) :=
      FourColorKernels.unit_integrable _ _ (by fun_prop) (fun x => hb i (x,z))
    unfold flux
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    have he : (fun x => ∑ i, W i (x,z)) =ᵐ[μ.restrict X] (fun _ => (1:ℝ)) :=
      ae_restrict_of_ae hz
    rw [integral_congr_ae he]
    simp [t]
  have hl : ∀ᵐ z ∂μ, ∑ i : Fin 3, flux (μ.restrict X) (W i.succ) z=t*(1-f z) := by
    filter_upwards [hsum,h0] with z hz hzero
    have he : flux (μ.restrict X) (W 0) z +
        (∑ i : Fin 3, flux (μ.restrict X) (W i.succ) z)=t := by
      simpa only [Fin.sum_univ_succ] using hz
    rw [hzero] at he
    linarith
  exact indicator_flux_compensation X W hW hb hs f hf bf hfi t h0 hl
end FourColorTwinBlock

-- Module: FourColorGlobalGap
open MeasureTheory

namespace Submissions.E811FourColorParity.GlobalGap

/-- Compensation on countably many disjoint blocks forces the nonnegative
remainder of a zero-mean gap to vanish. -/
theorem zero_off_blocks {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (g : Ω → ℝ) (s : ι → Set Ω)
    (hg : Integrable g μ) (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hblocks : ∀ i, 0 ≤ ∫ x in s i, g x ∂μ)
    (hoff : ∀ᵐ x ∂μ.restrict (⋃ i, s i)ᶜ, 0 ≤ g x)
    (htotal : ∫ x, g x ∂μ = 0) :
    ∀ᵐ x ∂μ.restrict (⋃ i, s i)ᶜ, g x = 0 := by
  have hU : MeasurableSet (⋃ i, s i) := MeasurableSet.iUnion hm
  have hiU : 0 ≤ ∫ x in ⋃ i, s i, g x ∂μ := by
    rw [integral_iUnion hm hd hg.integrableOn]
    exact tsum_nonneg hblocks
  have hiC : 0 ≤ ∫ x in (⋃ i, s i)ᶜ, g x ∂μ := integral_nonneg_of_ae hoff
  have hsum := integral_add_compl hU hg
  have hz : (∫ x in (⋃ i, s i)ᶜ, g x ∂μ) = 0 := by linarith
  exact (integral_eq_zero_iff_of_nonneg_ae hoff hg.integrableOn).mp hz

end Submissions.E811FourColorParity.GlobalGap

-- Module: FourColorClasses
open MeasureTheory
namespace FourColorClasses
variable {Ω : Type*} [MeasurableSpace Ω]

theorem countable_positive_disjoint_family (μ : Measure Ω) [SFinite μ]
    (C : Set (Set Ω))
    (hm : ∀ S ∈ C, MeasurableSet S)
    (hp : ∀ S ∈ C, 0 < μ S)
    (hd : C.PairwiseDisjoint id) : C.Countable := by
  have hh : Set.Countable {i : C | 0 < μ i.val} :=
    Measure.countable_meas_pos_of_disjoint_iUnion
      (fun i => hm i.val i.property)
      (fun i j hij => hd i.property j.property (fun he => hij (Subtype.ext he)))
  have hu : {i : C | 0 < μ i.val} = Set.univ := by
    ext i
    simp [hp i.val i.property]
  rw [hu] at hh
  exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hh)

def classSet (G : Set Ω) (R : Ω → Ω → Prop) (x : Ω) : Set Ω :=
  {y | y ∈ G ∧ R x y}

def classFamily (G : Set Ω) (R : Ω → Ω → Prop) : Set (Set Ω) :=
  {S | ∃ x ∈ G, S = classSet G R x}

theorem positive_equivalence_partition (μ : Measure Ω) [SFinite μ]
    (G : Set Ω) (R : Ω → Ω → Prop)
    (hrefl : ∀ x ∈ G, R x x)
    (hsymm : ∀ x ∈ G, ∀ y ∈ G, R x y → R y x)
    (htrans : ∀ x ∈ G, ∀ y ∈ G, ∀ z ∈ G, R x y → R y z → R x z)
    (hmeas : ∀ x ∈ G, MeasurableSet (classSet G R x))
    (hpos : ∀ x ∈ G, 0 < μ (classSet G R x)) :
    (classFamily G R).Countable ∧
    (∀ S ∈ classFamily G R, MeasurableSet S ∧ 0 < μ S) ∧
    (classFamily G R).PairwiseDisjoint id ∧
    ⋃₀ classFamily G R = G := by
  have hm : ∀ S ∈ classFamily G R, MeasurableSet S ∧ 0 < μ S := by
    rintro S ⟨x,hx,rfl⟩
    exact ⟨hmeas x hx,hpos x hx⟩
  have hd : (classFamily G R).PairwiseDisjoint id := by
    intro S hS T hT hne
    obtain ⟨x,hx,rfl⟩ := hS
    obtain ⟨y,hy,rfl⟩ := hT
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hxy : R x y := htrans x hx z hz.1 y hy hz.2 (hsymm y hy z hz'.1 hz'.2)
    apply hne
    ext w
    constructor
    · intro hw
      exact ⟨hw.1,htrans y hy x hx w hw.1 (hsymm x hx y hy hxy) hw.2⟩
    · intro hw
      exact ⟨hw.1,htrans x hx y hy w hw.1 hxy hw.2⟩
  refine ⟨countable_positive_disjoint_family μ _ (fun S hS => (hm S hS).1)
    (fun S hS => (hm S hS).2) hd,hm,hd,?_⟩
  ext x
  constructor
  · rintro ⟨S,⟨y,hy,rfl⟩,hx⟩
    exact hx.1
  · intro hx
    exact Set.mem_sUnion.mpr ⟨classSet G R x,⟨x,hx,rfl⟩,⟨hx,hrefl x hx⟩⟩

end FourColorClasses

-- Module: FourColorOffBlock
open MeasureTheory
namespace FourColorOffBlock
open FourColorKernels FourColorKernelMatrix
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def gap (W : Fin 4 → Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  3 * (∑ i : Fin 3, comp μ (W i.succ) (W i.succ) p) - comp μ (W 0) (W 0) p

lemma comp_integrable (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] (i : Fin 4) :
    Integrable (comp μ (W i) (W i)) ν :=
  unit_integrable ν _ (measurable_comp μ _ _ (hm i) (hm i))
    (comp_bounds μ _ _ (hm i) (hm i) (hb i) (hb i))

lemma gap_integrable (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable (gap (μ := μ) W) ν :=
  ((integrable_finsetSum _ (fun i _ => comp_integrable W hm hb ν i.succ)).const_mul 3).sub
    (comp_integrable W hm hb ν 0)

lemma twin_gap_nonneg (X : Set Ω) (hX : MeasurableSet X)
    (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ i, W i p=1)
    (f : Ω → ℝ) (hf : Measurable f) (bf : ∀ᵐ z ∂μ, f z=0 ∨ f z=1)
    (hfi : ∫ z, f z ∂μ = (1:ℝ)/2)
    (htwin : ∀ᵐ x ∂μ.restrict X, ∀ᵐ z ∂μ, W 0 (x,z)=f z) :
    0 ≤ ∫ p in X ×ˢ X, gap (μ := μ) W p ∂μ.prod μ := by
  have h := FourColorTwinBlock.twin_block_compensation X W hm hb hs ht f hf bf hfi htwin
  rw [← Measure.prod_restrict]
  unfold gap
  rw [integral_sub ((integrable_finsetSum _ (fun i _ => comp_integrable W hm hb _ i.succ)).const_mul 3)
      (comp_integrable W hm hb _ 0), integral_const_mul,
    integral_finsetSum _ (fun i _ => comp_integrable W hm hb _ i.succ)]
  linarith

lemma off_blocks_zero {ι : Type*} [Countable ι]
    (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ i, W i p=1)
    (hr : ∀ i, ∀ᵐ x ∂μ, ∫ y, W i (x,y) ∂μ = if i=0 then (1:ℝ)/2 else 1/6)
    (hz : ∀ᵐ p ∂μ.prod μ,
      M (μ := μ) W 0 1 p * M (μ := μ) W 2 3 p = 0 ∧
      M (μ := μ) W 0 2 p * M (μ := μ) W 1 3 p = 0 ∧
      M (μ := μ) W 0 3 p * M (μ := μ) W 1 2 p = 0)
    (X : ι → Set Ω) (hX : ∀ i, MeasurableSet (X i))
    (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (bf : ∀ i, ∀ᵐ z ∂μ, f i z=0 ∨ f i z=1)
    (hfi : ∀ i, ∫ z, f i z ∂μ = (1:ℝ)/2)
    (htwin : ∀ i, ∀ᵐ x ∂μ.restrict (X i), ∀ᵐ z ∂μ, W 0 (x,z)=f i z)
    (hunsat : ∀ᵐ p ∂(μ.prod μ).restrict (⋃ i, X i ×ˢ X i)ᶜ,
      comp μ (W 0) (W 0) p < 1/2) :
    ∀ᵐ p ∂(μ.prod μ).restrict (⋃ i, X i ×ˢ X i)ᶜ,
      comp μ (W 0) (W 0) p = 0 := by
  let d : Fin 4 → ℝ := fun i => if i=0 then 1/2 else 1/6
  have hmar := ae_all_iff.mpr (fun i => M_marginal (μ := μ) W hm hb hs ht d hr i)
  have hlocal : ∀ᵐ p ∂(μ.prod μ).restrict (⋃ i, X i ×ˢ X i)ᶜ,
      0 ≤ gap (μ := μ) W p ∧ (gap (μ := μ) W p=0 → comp μ (W 0) (W 0) p=0) := by
    filter_upwards [ae_restrict_of_ae hmar,ae_restrict_of_ae hz,hunsat] with p hp hpz hpa
    have hh := Submissions.E811FourColorParity.Transport.matrix_gap
      (fun i j => M (μ := μ) W i j p)
      (fun i j => (M_bounds (μ := μ) W hm hb i j p).1)
      (fun i j => congrFun (M_label_symm (μ := μ) W i j) p)
      hp hpz.1 hpz.2.1 hpz.2.2 (by simpa only [M,add_self_div_two] using hpa)
    simpa [gap,M,add_self_div_two,Fin.sum_univ_succ,add_assoc] using hh
  have hmoment (i : Fin 4) :
      (∫ p, comp μ (W i) (W i) p ∂μ.prod μ)=d i*d i := by
    rw [integral_prod _ (comp_integrable W hm hb _ i)]
    have hi := comp_row μ (W i) (W i) (hm i) (hm i) (hb i) (hb i) (d i) (d i) (hr i) (hr i)
    rw [integral_congr_ae hi]
    simp
  have htotal : (∫ p, gap (μ := μ) W p ∂μ.prod μ)=0 := by
    unfold gap
    rw [integral_sub ((integrable_finsetSum _ (fun i _ => comp_integrable W hm hb _ i.succ)).const_mul 3)
        (comp_integrable W hm hb _ 0),integral_const_mul,
      integral_finsetSum _ (fun i _ => comp_integrable W hm hb _ i.succ)]
    simp_rw [hmoment]
    norm_num [d,Fin.sum_univ_succ]
  have hdis : Pairwise (fun i j => Disjoint (X i ×ˢ X i) (X j ×ˢ X j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (hd hij) hp.1 hq.1
  have hg := Submissions.E811FourColorParity.GlobalGap.zero_off_blocks (μ.prod μ)
    (gap (μ := μ) W) (fun i => X i ×ˢ X i) (gap_integrable W hm hb _)
    (fun i => (hX i).prod (hX i)) hdis
    (fun i => twin_gap_nonneg (X i) (hX i) W hm hb hs ht (f i) (hf i) (bf i) (hfi i) (htwin i))
    (hlocal.mono (fun _ h => h.1)) htotal
  filter_upwards [hlocal,hg] with p hp hpg
  exact hp.2 hpg
end FourColorOffBlock
namespace FourColorOffBlock
open FourColorKernels FourColorKernelMatrix FourColorClasses
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma off_twin_classes_zero
    (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ i, W i p=1)
    (hr : ∀ i, ∀ᵐ x ∂μ, ∫ y, W i (x,y) ∂μ = if i=0 then (1:ℝ)/2 else 1/6)
    (hz : ∀ᵐ p ∂μ.prod μ,
      M (μ := μ) W 0 1 p * M (μ := μ) W 2 3 p = 0 ∧
      M (μ := μ) W 0 2 p * M (μ := μ) W 1 3 p = 0 ∧
      M (μ := μ) W 0 3 p * M (μ := μ) W 1 2 p = 0)
    (G : Set Ω) (hG : MeasurableSet G) (hGa : ∀ᵐ x ∂μ, x ∈ G)
    (hgood : ∀ x ∈ G,
      (∫ z, W 0 (x,z) ∂μ = (1:ℝ)/2) ∧
      (∀ᵐ z ∂μ, W 0 (x,z)=0 ∨ W 0 (x,z)=1) ∧
      0 < μ {y | y ∈ G ∧ (fun z => W 0 (x,z)) =ᵐ[μ] (fun z => W 0 (y,z))}) :
    ∀ᵐ p ∂μ.prod μ,
      (¬ (fun z => W 0 (p.1,z)) =ᵐ[μ] (fun z => W 0 (p.2,z))) →
      comp μ (W 0) (W 0) p=0 := by
  classical
  let R := fun x y => (fun z => W 0 (x,z)) =ᵐ[μ] (fun z => W 0 (y,z))
  have he := FourColorRowDistance.twin_equivalence μ (W 0)
  have hmeas (x : Ω) : MeasurableSet (classSet G R x) :=
    hG.inter (FourColorRowDistance.measurable_twin_class μ (W 0) (hm 0) (hb 0) x)
  obtain ⟨hc,hmem,hd,hcover⟩ := positive_equivalence_partition μ G R
    (fun x _ => he.refl x) (fun x _ y _ h => he.symm h)
    (fun x _ y _ z _ h k => he.trans h k) (fun x _ => hmeas x)
    (fun x hx => (hgood x hx).2.2)
  let I := ↥(classFamily G R)
  letI : Countable I := hc.to_subtype
  let X : I → Set Ω := fun i => i.val
  have hrep : ∀ i : I, ∃ x ∈ G, X i=classSet G R x := fun i => i.property
  choose rep hrepG hrepEq using hrep
  have hXm (i : I) : MeasurableSet (X i) := (hmem _ i.property).1
  have hXd : Pairwise (fun i j : I => Disjoint (X i) (X j)) := by
    intro i j hij
    exact hd i.property j.property (fun h => hij (Subtype.ext h))
  let U : Set (Ω × Ω) := ⋃ i : I, X i ×ˢ X i
  have hU : MeasurableSet U := MeasurableSet.iUnion (fun i => (hXm i).prod (hXm i))
  have hcoverR (x y : Ω) (hx : x ∈ G) (hy : y ∈ G) (hxy : R x y) : (x,y) ∈ U := by
    let i : I := ⟨classSet G R x,⟨x,hx,rfl⟩⟩
    exact Set.mem_iUnion.mpr ⟨i,⟨⟨hx,he.refl x⟩,⟨hy,hxy⟩⟩⟩
  have hblockR (p : Ω × Ω) (hp : p ∈ U) : R p.1 p.2 := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    rw [hrepEq i] at hi
    exact he.trans (he.symm hi.1.2) hi.2.2
  have hGG : ∀ᵐ p ∂μ.prod μ, p.1 ∈ G ∧ p.2 ∈ G := by
    apply (Measure.ae_prod_iff_ae_ae (hG.prod hG)).mpr
    filter_upwards [hGa] with x hx
    exact hGa.mono (fun y hy => ⟨hx,hy⟩)
  have hmar := M_marginal (μ := μ) W hm hb hs ht
    (fun i => if i=0 then (1:ℝ)/2 else 1/6) hr 0
  have hunsat : ∀ᵐ p ∂(μ.prod μ).restrict Uᶜ, comp μ (W 0) (W 0) p < 1/2 := by
    apply (ae_restrict_iff' hU.compl).mpr
    filter_upwards [hGG,hmar] with p hp hmp
    intro hpu
    have hle : comp μ (W 0) (W 0) p ≤ 1/2 := by
      norm_num [Fin.sum_univ_succ] at hmp
      have h1 := (M_bounds (μ := μ) W hm hb 0 1 p).1
      have h2 := (M_bounds (μ := μ) W hm hb 0 2 p).1
      have h3 := (M_bounds (μ := μ) W hm hb 0 3 p).1
      have hdiag : M (μ := μ) W 0 0 p=comp μ (W 0) (W 0) p := by simp [M]
      rw [hdiag] at hmp
      change comp μ (W 0) (W 0) p + (M (μ := μ) W 0 1 p + (M (μ := μ) W 0 2 p + M (μ := μ) W 0 3 p)) = 1/2 at hmp
      linarith
    apply lt_of_le_of_ne hle
    intro heq
    have hpair := FourColorEqualRows.half_rows_equal_indicator μ
      (fun z => W 0 (p.1,z)) (fun z => W 0 (p.2,z))
      (by fun_prop) (by fun_prop)
      (Filter.Eventually.of_forall (fun z => hb 0 (p.1,z)))
      (Filter.Eventually.of_forall (fun z => hb 0 (p.2,z)))
      (hgood p.1 hp.1).1 (hgood p.2 hp.2).1
      (by simpa only [comp,hs] using heq)
    exact hpu (hcoverR p.1 p.2 hp.1 hp.2 (hpair.mono (fun _ h => h.1)))
  have hout := off_blocks_zero W hm hb hs ht hr hz X hXm hXd
    (fun i z => W 0 (rep i,z)) (fun i => by fun_prop)
    (fun i => (hgood _ (hrepG i)).2.1) (fun i => (hgood _ (hrepG i)).1)
    (fun i => (ae_restrict_iff' (hXm i)).mpr (Filter.Eventually.of_forall (fun x hx => by
      rw [hrepEq i] at hx
      exact hx.2.symm))) hunsat
  have hout' := (ae_restrict_iff' hU.compl).mp hout
  filter_upwards [hout'] with p hp
  intro hn
  exact hp (fun h => hn (hblockR p h))
end FourColorOffBlock

-- Module: FourColorHalfClass
open MeasureTheory
namespace FourColorHalfClass
variable {Ω : Type*} [MeasurableSpace Ω]
noncomputable def side (X : Set Ω) : Ω → ℝ := X.indicator (fun _ => 1)
noncomputable def sameSide (X : Set Ω) (p : Ω × Ω) : ℝ := by
  classical
  exact if (p.1 ∈ X ↔ p.2 ∈ X) then 1 else 0


lemma measurable_sameSide (X : Set Ω) (hX : MeasurableSet X) : Measurable (sameSide X) := by
  classical
  have he : {p : Ω × Ω | p.1 ∈ X ↔ p.2 ∈ X} =
      ({p | p.1 ∈ X} ∩ {p | p.2 ∈ X}) ∪
      ({p | p.1 ∈ X}ᶜ ∩ {p | p.2 ∈ X}ᶜ) := by
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
    tauto
  have hc : MeasurableSet {p : Ω × Ω | p.1 ∈ X ↔ p.2 ∈ X} := by
    rw [he]
    exact ((hX.preimage measurable_fst).inter (hX.preimage measurable_snd)).union
      ((hX.preimage measurable_fst).compl.inter (hX.preimage measurable_snd).compl)
  exact Measurable.ite hc measurable_const measurable_const

lemma integral_side (μ : Measure Ω) (X : Set Ω) (hX : MeasurableSet X)
    (hμ : μ X = (1:ENNReal)/2) : ∫ x, side X x ∂μ = (1:ℝ)/2 := by
  rw [side,integral_indicator_const (1:ℝ) hX]
  simp [Measure.real,hμ]

lemma complete_half_row (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Set Ω) (hX : MeasurableSet X) (hμ : μ X = (1:ENNReal)/2)
    (g : Ω → ℝ) (hg : Measurable g) (bg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hgi : ∫ x, g x ∂μ = (1:ℝ)/2)
    (b : ℝ) (hb : b=0 ∨ b=1)
    (he : ∀ᵐ x ∂μ, x ∈ X → g x=b) :
    (b=1 ∧ g =ᵐ[μ] side X) ∨ (b=0 ∧ g =ᵐ[μ] side Xᶜ) := by
  classical
  have ig := FourColorEqualRows.unit_integrable μ g hg (Filter.Eventually.of_forall bg)
  have is (S : Set Ω) (hS : MeasurableSet S) : Integrable (side S) μ :=
    (integrable_const (1:ℝ)).indicator hS
  rcases hb with rfl | rfl
  · right
    refine ⟨rfl,?_⟩
    have hcomp : μ Xᶜ = (1:ENNReal)/2 := by
      rw [measure_compl hX (measure_ne_top μ X),measure_univ,hμ]
      norm_num
    apply (integral_eq_iff_of_ae_le ig (is Xᶜ hX.compl) ?_).mp
    · rw [hgi,integral_side μ Xᶜ hX.compl hcomp]
    · filter_upwards [he] with x hx
      by_cases hm : x ∈ X
      · simp [side,hm,hx hm]
      · simpa [side,hm] using (bg x).2
  · left
    refine ⟨rfl,?_⟩
    apply Filter.EventuallyEq.symm
    apply (integral_eq_iff_of_ae_le (is X hX) ig ?_).mp
    · rw [hgi,integral_side μ X hX hμ]
    · filter_upwards [he] with x hx
      by_cases hm : x ∈ X
      · simp [side,hm,hx hm]
      · simpa [side,hm] using (bg x).1

theorem parity_of_half_twin_class (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω × Ω → ℝ) (hm : Measurable A)
    (hb : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (hs : ∀ x y, A (x,y)=A (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y, A (x,y) ∂μ = (1:ℝ)/2)
    (X : Set Ω) (hX : MeasurableSet X) (hμ : μ X=(1:ENNReal)/2)
    (f : Ω → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ x ∂μ, f x=0 ∨ f x=1)
    (htwin : ∀ x ∈ X, (fun y => A (x,y)) =ᵐ[μ] f) :
    (A =ᵐ[μ.prod μ] sameSide X) ∨
    (A =ᵐ[μ.prod μ] (fun p => 1-sameSide X p)) := by
  classical
  have he : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, x ∈ X → A (x,y)=f y := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ X
    · exact (htwin x hx).mono (fun y hy _ => hy)
    · exact Filter.Eventually.of_forall (fun _ h => (hx h).elim)
  have he' : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, x ∈ X → A (x,y)=f y := by
    apply (Measure.ae_ae_comm ?_).mp he
    have hh : MeasurableSet {p : Ω × Ω | p.1 ∈ X → A p=f p.2} := by
      have hset : {p : Ω × Ω | p.1 ∈ X → A p=f p.2} =
          {p : Ω × Ω | p.1 ∈ X}ᶜ ∪ {p | A p=f p.2} := by
        ext p
        simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,imp_iff_not_or]
      rw [hset]
      exact (hX.preimage measurable_fst).compl.union (measurableSet_eq_fun hm (hf.comp measurable_snd))
    exact hh
  have hforms : ∀ᵐ y ∂μ,
      (f y=1 ∧ (fun x => A (y,x)) =ᵐ[μ] side X) ∨
      (f y=0 ∧ (fun x => A (y,x)) =ᵐ[μ] side Xᶜ) := by
    filter_upwards [he',hr,hfb] with y hy hyr hyb
    apply complete_half_row μ X hX hμ (fun x => A (y,x)) (by fun_prop)
      (fun x => hb (y,x)) hyr (f y) hyb
    filter_upwards [hy] with x hx
    intro hxx
    rw [hs y x]
    exact hx hxx
  have hfreq : ∃ᶠ x in ae μ, x ∈ X := frequently_ae_iff.mpr (by change μ X ≠ 0; rw [hμ]; norm_num)
  obtain ⟨x,hx,hform⟩ := (hfreq.and_eventually hforms).exists
  have hfid : (f =ᵐ[μ] side X) ∨ (f =ᵐ[μ] side Xᶜ) := by
    rcases hform with h | h
    · exact Or.inl ((htwin x hx).symm.trans h.2)
    · exact Or.inr ((htwin x hx).symm.trans h.2)
  rcases hfid with hfid | hfid
  · left
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [hforms,hfid] with x hx hfx
      rcases hx with h | h
      · have hxx : x ∈ X := by by_contra hn; simp [side,hn] at hfx; linarith [h.1]
        filter_upwards [h.2] with y hy
        by_cases hyX : y ∈ X <;> simpa [sameSide,side,hxx,hyX] using hy
      · have hxx : x ∉ X := by intro hn; simp [side,hn] at hfx; linarith [h.1]
        filter_upwards [h.2] with y hy
        by_cases hyX : y ∈ X <;> simpa [sameSide,side,hxx,hyX] using hy
    · apply measurableSet_eq_fun hm
      exact measurable_sameSide X hX
  · right
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [hforms,hfid] with x hx hfx
      rcases hx with h | h
      · have hxx : x ∉ X := by intro hn; simp [side,hn] at hfx; linarith [h.1]
        filter_upwards [h.2] with y hy
        by_cases hyX : y ∈ X <;> simpa [sameSide,side,hxx,hyX] using hy
      · have hxx : x ∈ X := by by_contra hn; simp [side,hn] at hfx; linarith [h.1]
        filter_upwards [h.2] with y hy
        by_cases hyX : y ∈ X <;> simpa [sameSide,side,hxx,hyX] using hy
    · apply measurableSet_eq_fun hm
      exact measurable_const.sub (measurable_sameSide X hX)

end FourColorHalfClass


-- Module: FourColorClassMass
open MeasureTheory
namespace Submissions.E811FourColorParity.ClassMass

/-- The fixed overlap-row integral determines the mass of its twin class. -/
theorem half_mass_of_indicator_row {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Set Ω) (hX : MeasurableSet X)
    (a : Ω → ℝ) (hr : ∫ y, a y ∂μ = (1:ℝ)/4)
    (he : a =ᵐ[μ] X.indicator (fun _ => (1:ℝ)/2)) :
    μ X = (1:ENNReal)/2 := by
  have hi := integral_congr_ae he
  rw [hr,integral_indicator_const ((1:ℝ)/2) hX] at hi
  have hm : μ.real X = (1:ℝ)/2 := by
    simp only [smul_eq_mul] at hi
    linarith
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ X) (by simp)).mp
  simpa [measureReal_def] using hm

end Submissions.E811FourColorParity.ClassMass

-- Module: FourColorParityFromOff
open MeasureTheory
namespace FourColorParityFromOff
variable {Ω : Type*} [MeasurableSpace Ω]

theorem parity_of_off_twin_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω × Ω → ℝ) (hm : Measurable A)
    (hb : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (hs : ∀ x y, A (x,y)=A (y,x))
    (G : Set Ω) (hG : MeasurableSet G) (hGa : ∀ᵐ x ∂μ, x ∈ G)
    (hgood : ∀ x ∈ G,
      (∫ y, A (x,y) ∂μ = (1:ℝ)/2) ∧
      (∀ᵐ z ∂μ, A (x,z)=0 ∨ A (x,z)=1))
    (hr : ∀ᵐ x ∂μ, ∫ y, FourColorKernels.comp μ A A (x,y) ∂μ = (1:ℝ)/4)
    (hoff : ∀ᵐ p ∂μ.prod μ,
      (¬ (fun z => A (p.1,z)) =ᵐ[μ] (fun z => A (p.2,z))) →
      FourColorKernels.comp μ A A p=0) :
    ∃ X : Set Ω, MeasurableSet X ∧ μ X=(1:ENNReal)/2 ∧
      ((A =ᵐ[μ.prod μ] FourColorHalfClass.sameSide X) ∨
       (A =ᵐ[μ.prod μ] (fun p => 1-FourColorHalfClass.sameSide X p))) := by
  classical
  obtain ⟨x,hx,hxr,hxo⟩ := (hGa.and (hr.and (Measure.ae_ae_of_ae_prod hoff))).exists
  let X : Set Ω := {y | y ∈ G ∧ (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z))}
  have hX : MeasurableSet X := hG.inter (FourColorRowDistance.measurable_twin_class μ A hm hb x)
  have he : (fun y => FourColorKernels.comp μ A A (x,y)) =ᵐ[μ]
      X.indicator (fun _ => (1:ℝ)/2) := by
    filter_upwards [hGa,hxo] with y hy hyo
    by_cases ht : (fun z => A (x,z)) =ᵐ[μ] (fun z => A (y,z))
    · have hcomp : FourColorKernels.comp μ A A (x,y)=(1:ℝ)/2 := by
        calc
          _ = ∫ z, A (x,z) ∂μ := by
            apply integral_congr_ae
            filter_upwards [ht,(hgood x hx).2] with z hz hzb
            change A (x,z)*A (z,y)=A (x,z)
            rw [hs z y,← hz]
            rcases hzb with h | h <;> simp [h]
          _ = _ := (hgood x hx).1
      simpa [X,hy,ht] using hcomp
    · have hh := hyo ht
      simpa [X,hy,ht] using hh
  have hmass := Submissions.E811FourColorParity.ClassMass.half_mass_of_indicator_row
    μ X hX (fun y => FourColorKernels.comp μ A A (x,y)) hxr he
  refine ⟨X,hX,hmass,?_⟩
  apply FourColorHalfClass.parity_of_half_twin_class μ A hm hb hs
    (hGa.mono (fun y hy => (hgood y hy).1)) X hX hmass
    (fun z => A (x,z)) (by fun_prop) (hgood x hx).2
  intro y hy
  exact hy.2.symm

end FourColorParityFromOff

-- Module: FourColorNormalization
open MeasureTheory
namespace Submissions.E811FourColorParity.Normalization
open Submissions.E811FourColorParity.Representatives

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma sum_congr_ae (W V : Fin 4 → Ω × Ω → ℝ)
    (he : ∀ i, V i =ᵐ[μ.prod μ] W i)
    (hs : ∀ᵐ p ∂μ.prod μ, ∑ i, W i p = 1) :
    ∀ᵐ p ∂μ.prod μ, ∑ i, V i p = 1 := by
  filter_upwards [ae_all_iff.mpr he,hs] with p hp hs
  simpa only [hp] using hs

lemma row_congr_ae (W V : Fin 4 → Ω × Ω → ℝ)
    (he : ∀ i, V i =ᵐ[μ.prod μ] W i) (d : Fin 4 → ℝ)
    (hr : ∀ i, ∀ᵐ x ∂μ, ∫ y, W i (x,y) ∂μ = d i) :
    ∀ i, ∀ᵐ x ∂μ, ∫ y, V i (x,y) ∂μ = d i := by
  intro i
  filter_upwards [Measure.ae_ae_of_ae_prod (he i),hr i] with x hx hrx
  exact (integral_congr_ae hx).trans hrx

lemma cycles_congr (W V : Fin 4 → Ω × Ω → ℝ)
    (he : ∀ i, V i =ᵐ[μ.prod μ] W i)
    (hc : ∀ σ : Equiv.Perm (Fin 4),
      cycle4 μ (W (σ 0)) (W (σ 1)) (W (σ 2)) (W (σ 3)) = 0) :
    ∀ σ : Equiv.Perm (Fin 4),
      cycle4 μ (V (σ 0)) (V (σ 1)) (V (σ 2)) (V (σ 3)) = 0 := by
  intro σ
  exact (cycle4_congr μ (he _) (he _) (he _) (he _)).trans (hc σ)

end Submissions.E811FourColorParity.Normalization

-- Module: FourColorAssembly
open MeasureTheory
open scoped BigOperators

namespace Submissions.E811FourColorParity.Complete
open Submissions.E811FourColorParity.Representatives

/-- The full structural theorem for pointwise bounded symmetric representatives. -/
theorem pointwise {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (ht : ∀ᵐ p ∂μ.prod μ, ∑ i, W i p=1)
    (hr : ∀ i, ∀ᵐ x ∂μ, ∫ y, W i (x,y) ∂μ = if i=0 then (1:ℝ)/2 else 1/6)
    (hc : ∀ σ : Equiv.Perm (Fin 4),
      cycle4 μ (W (σ 0)) (W (σ 1)) (W (σ 2)) (W (σ 3))=0) :
    ∃ X : Set Ω, MeasurableSet X ∧ μ X=(1:ENNReal)/2 ∧
      ((W 0 =ᵐ[μ.prod μ] FourColorHalfClass.sameSide X) ∨
       (W 0 =ᵐ[μ.prod μ] (fun p => 1-FourColorHalfClass.sameSide X p))) := by
  have hz := FourColorCycleMatrix.complementary_M_products_zero W hm hb hs hc
  have hp := FourColorSaturationBridge.positive_saturation_fibers μ W hm hb hs ht hr hz
  have hrow : ∀ᵐ x ∂μ, ∫ y, W 0 (x,y) ∂μ = (1:ℝ)/2 := by simpa using hr 0
  obtain ⟨G,hG,hGa,hgood⟩ := FourColorTwinExtraction.extract_twins μ (W 0)
    (hm 0) (hb 0) (hs 0) hrow hp
  have hoff := FourColorOffBlock.off_twin_classes_zero W hm hb hs ht hr hz G hG hGa hgood
  have hmoment := FourColorKernels.comp_row μ (W 0) (W 0) (hm 0) (hm 0)
    (hb 0) (hb 0) ((1:ℝ)/2) ((1:ℝ)/2) hrow hrow
  have hmoment' : ∀ᵐ x ∂μ, ∫ y, FourColorKernels.comp μ (W 0) (W 0) (x,y) ∂μ = (1:ℝ)/4 := by
    convert hmoment using 1 <;> norm_num
  exact FourColorParityFromOff.parity_of_off_twin_zero μ (W 0) (hm 0) (hb 0) (hs 0)
    G hG hGa (fun x hx => ⟨(hgood x hx).1,(hgood x hx).2.1⟩) hmoment' hoff

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 4)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₀) ∂μ ∂μ ∂μ ∂μ

noncomputable def sameSide {Ω : Type*} (S : Set Ω) (p : Ω × Ω) : ℝ := by
  classical
  exact if (p.1 ∈ S ↔ p.2 ∈ S) then 1 else 0

/-- Exact almost-everywhere canonical target, with no additional hypotheses. -/
theorem target :
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 4 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂(μ.prod μ), ∑ c : Fin 4, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x, y) ∂μ =
        if c = 0 then (1 : ℝ) / 2 else (1 : ℝ) / 6) →
      (∀ σ : Equiv.Perm (Fin 4), cycleDensity μ W σ = 0) →
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = (1 : ENNReal) / 2 ∧
        ((∀ᵐ p ∂(μ.prod μ), W 0 p = sameSide S p) ∨
         (∀ᵐ p ∂(μ.prod μ), W 0 p = 1 - sameSide S p)) := by
  intro Ω _ μ hμ W hm hb hs ht hr hc
  letI : IsProbabilityMeasure μ := hμ
  let V : Fin 4 → Ω × Ω → ℝ := fun i => symclip (W i)
  have he : ∀ i, V i =ᵐ[μ.prod μ] W i := fun i => symclip_eq_ae μ (W i) (hb i) (hs i)
  have hVm : ∀ i, Measurable (V i) := fun i => measurable_symclip (hm i)
  have hVb : ∀ i p, 0 ≤ V i p ∧ V i p ≤ 1 := fun i p => symclip_bounds (W i) p
  have hVs : ∀ i x y, V i (x,y)=V i (y,x) := fun i x y => symclip_symm (W i) (x,y)
  have hVt := Submissions.E811FourColorParity.Normalization.sum_congr_ae μ W V he ht
  have hVr := Submissions.E811FourColorParity.Normalization.row_congr_ae μ W V he
    (fun i => if i=0 then (1:ℝ)/2 else 1/6) hr
  have hWc : ∀ σ : Equiv.Perm (Fin 4), cycle4 μ (W (σ 0)) (W (σ 1)) (W (σ 2)) (W (σ 3))=0 := hc
  have hVc := Submissions.E811FourColorParity.Normalization.cycles_congr μ W V he hWc
  obtain ⟨S,hSm,hSμ,hSp⟩ := pointwise μ V hVm hVb hVs hVt hVr hVc
  refine ⟨S,hSm,hSμ,?_⟩
  rcases hSp with h | h
  · exact Or.inl ((he 0).symm.trans h)
  · exact Or.inr ((he 0).symm.trans h)

end Submissions.E811FourColorParity.Complete
