import Mathlib

namespace Submissions.E811TwoPairParity.Complete
end Submissions.E811TwoPairParity.Complete


-- Local module: FourColorRepresentatives
section
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
end


-- Local module: TwoPairNormalization
section
open MeasureTheory
namespace TwoPairNormalization
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def cycle6 (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W 0 (x₀,x₁)*W 1 (x₁,x₂)*W 2 (x₂,x₃)*W 3 (x₃,x₄)*
      W 4 (x₄,x₅)*W 5 (x₅,x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

lemma cycle6_congr (μ : Measure Ω) [SFinite μ]
    (W V : Fin 6 → Ω × Ω → ℝ) (he : ∀ c, V c =ᵐ[μ.prod μ] W c) :
    cycle6 μ V = cycle6 μ W := by
  have hlast := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq (he 5))
  unfold cycle6
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (he 0),hlast] with x₀ h0 h5
  apply integral_congr_ae
  filter_upwards [h0,Measure.ae_ae_of_ae_prod (he 1)] with x₁ h01 h1
  apply integral_congr_ae
  filter_upwards [h1,Measure.ae_ae_of_ae_prod (he 2)] with x₂ h12 h2
  apply integral_congr_ae
  filter_upwards [h2,Measure.ae_ae_of_ae_prod (he 3)] with x₃ h23 h3
  apply integral_congr_ae
  filter_upwards [h3,Measure.ae_ae_of_ae_prod (he 4)] with x₄ h34 h4
  apply integral_congr_ae
  filter_upwards [h4,h5] with x₅ h45 h50
  change V 5 (x₅,x₀) = W 5 (x₅,x₀) at h50
  rw [h01,h12,h23,h34,h45,h50]

/-- Repair the null weighted-partition defect after symmetric clipping. -/
theorem normalize (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω × Ω → ℝ) (hm : ∀ c, Measurable (W c))
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hs : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hp : ∀ᵐ p ∂μ.prod μ, 2*W 0 p+2*W 1 p+W 2 p+W 3 p=1) :
    ∃ V : Fin 4 → Ω × Ω → ℝ,
      (∀ c, Measurable (V c)) ∧
      (∀ c p, 0 ≤ V c p ∧ V c p ≤ 1) ∧
      (∀ c p, V c p = V c (p.2,p.1)) ∧
      (∀ p, 2*V 0 p+2*V 1 p+V 2 p+V 3 p=1) ∧
      (∀ c, V c =ᵐ[μ.prod μ] W c) ∧
      (∀ p, V 0 p+V 1 p ≤ (1/2:ℝ) ∧ V 2 p+V 3 p ≤ 1) ∧
      (∀ c, ∀ᵐ x ∂μ, (∫ y, V c (x,y) ∂μ) = ∫ y, W c (x,y) ∂μ) ∧
      (∀ word : Fin 6 → Fin 4, cycle6 μ (fun i => V (word i)) =
        cycle6 μ (fun i => W (word i))) := by
  classical
  let U : Fin 4 → Ω × Ω → ℝ := fun c => symclip (W c)
  have hUm (c) : Measurable (U c) := measurable_symclip (hm c)
  have hUb (c) (p) : 0 ≤ U c p ∧ U c p ≤ 1 := symclip_bounds (W c) p
  have hUs (c) (p) : U c p = U c (p.2,p.1) := symclip_symm (W c) p
  have hUe (c) : U c =ᵐ[μ.prod μ] W c := symclip_eq_ae μ (W c) (hb c) (hs c)
  let S : Set (Ω × Ω) := {p | 2*U 0 p+2*U 1 p+U 2 p+U 3 p=1}
  have hS : MeasurableSet S := measurableSet_eq_fun (by fun_prop) measurable_const
  have hSa : ∀ᵐ p ∂μ.prod μ, p ∈ S := by
    filter_upwards [ae_all_iff.mpr hUe,hp] with p he hp
    simpa only [S,Set.mem_setOf_eq,he] using hp
  have hSs (p : Ω × Ω) : p ∈ S ↔ (p.2,p.1) ∈ S := by
    change (2*U 0 p+2*U 1 p+U 2 p+U 3 p=1) ↔
      (2*U 0 (p.2,p.1)+2*U 1 (p.2,p.1)+U 2 (p.2,p.1)+U 3 (p.2,p.1)=1)
    rw [hUs 0 p,hUs 1 p,hUs 2 p,hUs 3 p]
  let V : Fin 4 → Ω × Ω → ℝ := fun c => S.piecewise (U c) (fun _ => 1/6)
  have hVm (c) : Measurable (V c) := (hUm c).piecewise hS measurable_const
  have hVb (c) (p) : 0 ≤ V c p ∧ V c p ≤ 1 := by
    by_cases h : p ∈ S
    · simpa [V,Set.piecewise,h] using hUb c p
    · norm_num [V,Set.piecewise,h]
  have hVs (c) (p : Ω × Ω) : V c p = V c (p.2,p.1) := by
    by_cases h : p ∈ S
    · simp only [V,Set.piecewise,h,(hSs p).mp h,if_pos]
      exact hUs c p
    · have h' : (p.2,p.1) ∉ S := fun hh => h ((hSs p).mpr hh)
      simp [V,Set.piecewise,h,h']
  have hVp (p) : 2*V 0 p+2*V 1 p+V 2 p+V 3 p=1 := by
    by_cases h : p ∈ S
    · have he : 2*U 0 p+2*U 1 p+U 2 p+U 3 p=1 := h
      simpa [V,Set.piecewise,h] using he
    · norm_num [V,Set.piecewise,h]
  have hVe (c) : V c =ᵐ[μ.prod μ] W c := by
    apply Filter.EventuallyEq.trans _ (hUe c)
    filter_upwards [hSa] with p hp
    simp [V,Set.piecewise,hp]
  refine ⟨V,hVm,hVb,hVs,hVp,hVe,?_,?_,?_⟩
  · intro p
    have h := hVp p
    have h0 := (hVb 0 p).1
    have h1 := (hVb 1 p).1
    have h2 := (hVb 2 p).1
    have h3 := (hVb 3 p).1
    constructor <;> linarith
  · intro c
    filter_upwards [Measure.ae_ae_of_ae_prod (hVe c)] with x hx
    exact integral_congr_ae hx
  · intro word
    exact cycle6_congr μ _ _ (fun i => hVe (word i))

end TwoPairNormalization
end


-- Local module: LowSupportAnalysis
section
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


end


-- Local module: LowSupportCycle
section
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
end


-- Local module: TwoPairWords
section
open MeasureTheory
namespace TwoPairWords
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
def color : Fin 6 → Fin 4 := ![0,0,1,1,2,3]

lemma zero_of_permutation (W : Fin 4 → Ω × Ω → ℝ)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (color (σ i)))=0)
    (f : Fin 6 → Fin 6) (hf : Function.Bijective f) :
    LowSupportCycle.cycleNested (μ := μ) (fun i => W (color (f i)))=0 :=
  hz (Equiv.ofBijective f hf)

lemma mixed_words (W : Fin 4 → Ω × Ω → ℝ)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (color (σ i)))=0) (t a b : Bool) :
    LowSupportCycle.cycleNested (μ := μ)
      ![if t then W 2 else W 3,if t then W 3 else W 2,
        if b then W 1 else W 0,if b then W 0 else W 1,
        if a then W 1 else W 0,if a then W 0 else W 1]=0 := by
  let f : Fin 6 → Fin 6 := ![if t then 4 else 5,if t then 5 else 4,
    if b then 2 else 0,if b then 0 else 2,
    if a then 3 else 1,if a then 1 else 3]
  have hf : Function.Bijective f := by
    cases t <;> cases a <;> cases b <;> decide
  have h := zero_of_permutation μ W hz f hf
  have he : (fun i => W (color (f i))) =
      ![if t then W 2 else W 3,if t then W 3 else W 2,
        if b then W 1 else W 0,if b then W 0 else W 1,
        if a then W 1 else W 0,if a then W 0 else W 1] := by
    funext i
    cases t <;> cases a <;> cases b <;> fin_cases i <;>
      rfl
  rwa [he] at h

lemma singleton_word (W : Fin 4 → Ω × Ω → ℝ)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (color (σ i)))=0) :
    LowSupportCycle.cycleNested (μ := μ) ![W 0,W 1,W 2,W 3,W 1,W 0]=0 := by
  have h := zero_of_permutation μ W hz ![0,2,4,5,3,1] (by decide)
  have he : (fun i => W (color (![0,2,4,5,3,1] i))) =
      ![W 0,W 1,W 2,W 3,W 1,W 0] := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at h
end TwoPairWords
end


-- Local module: FourColorKernels
section
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
end


-- Local module: TwoPairHalfSupport
section
open MeasureTheory
namespace TwoPairHalfSupport

lemma three_row_bound (a b c d e f : ℝ)
    (ha : 0 ≤ a+b) (hc : 0 ≤ c+d) (he : 0 ≤ e+f)
    (hA : a+b ≤ 1/2) (hC : c+d ≤ 1/2) (hE : e+f ≤ 1/2)
    (hac : a*c=0) (hbd : b*d=0)
    (haf : a*f=0) (hbe : b*e=0) (hcf : c*f=0) (hde : d*e=0) :
    (a+b)*(c+d) ≤ (1-2*(e+f))/4 := by
  have hz : (a+b)*(c+d)*(e+f)=0 := by
    linear_combination (e+f)*hac + (e+f)*hbd + a*hde + d*haf + c*hbe + b*hcf
  rcases mul_eq_zero.mp hz with hz | hz
  · rw [hz]
    linarith
  · have hh := mul_le_mul hA hC hc (by norm_num : (0:ℝ) ≤ 1/2)
    rw [hz]
    norm_num at hh ⊢
    exact hh

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- An endpoint row missing both mixed neighborhoods bounds the common two-path mass.
This is the strict-overlap contradiction in an integral form, avoiding support cardinality. -/
lemma overlap_bound_of_missing_row
    (a b c d e f : Ω → ℝ)
    (hm : ∀ g ∈ [a,b,c,d,e,f], Measurable g)
    (hb : ∀ᵐ z ∂μ,
      (0 ≤ a z+b z ∧ a z+b z ≤ 1/2) ∧
      (0 ≤ c z+d z ∧ c z+d z ≤ 1/2) ∧
      (0 ≤ e z+f z ∧ e z+f z ≤ 1/2))
    (hz : ∀ᵐ z ∂μ, a z*c z=0 ∧ b z*d z=0 ∧
      a z*f z=0 ∧ b z*e z=0 ∧ c z*f z=0 ∧ d z*e z=0)
    (hr : ∫ z, (e z+f z) ∂μ = (1:ℝ)/3) :
    (∫ z, (a z+b z)*(c z+d z) ∂μ) ≤ (1:ℝ)/12 := by
  have hma : Measurable a := hm a (by simp)
  have hmb : Measurable b := hm b (by simp)
  have hmc : Measurable c := hm c (by simp)
  have hmd : Measurable d := hm d (by simp)
  have hme : Measurable e := hm e (by simp)
  have hmf : Measurable f := hm f (by simp)
  have hi : Integrable (fun z => (a z+b z)*(c z+d z)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hb] with z h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.1.1 h.2.1.1)]
    nlinarith [mul_le_mul h.1.2 h.2.1.2 h.2.1.1 (by norm_num : (0:ℝ) ≤ 1/2)]
  have hefi : Integrable (fun z => e z+f z) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hb] with z h
    rw [Real.norm_eq_abs,abs_of_nonneg h.2.2.1]
    linarith [h.2.2.2]
  have hri : Integrable (fun z => (1-2*(e z+f z))/4) μ :=
    ((integrable_const (1:ℝ)).sub (hefi.const_mul 2)).div_const 4
  have hle : ∀ᵐ z ∂μ, (a z+b z)*(c z+d z) ≤ (1-2*(e z+f z))/4 := by
    filter_upwards [hb,hz] with z h k
    exact three_row_bound _ _ _ _ _ _ h.1.1 h.2.1.1 h.2.2.1
      h.1.2 h.2.1.2 h.2.2.2 k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2
  have hh := integral_mono_ae hi hri hle
  rw [integral_div,integral_sub (integrable_const _) (hefi.const_mul 2),integral_const_mul,hr] at hh
  norm_num at hh ⊢
  exact hh

end TwoPairHalfSupport
namespace TwoPairHalfSupport
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def supportRow (P : Ω × Ω → ℝ) (x y : Ω) : ℝ :=
  Set.indicator {z | 0 < P (x,z)} (fun _ => 1) y

lemma supportRow_measurable (P : Ω × Ω → ℝ) (hm : Measurable P) (x : Ω) :
    Measurable (supportRow P x) :=
  measurable_const.indicator (measurableSet_lt measurable_const
    (hm.comp (measurable_const.prodMk measurable_id)))

lemma supportRow_bounds (P : Ω × Ω → ℝ) (x y : Ω) :
    0 ≤ supportRow P x y ∧ supportRow P x y ≤ 1 := by
  classical
  by_cases h : 0 < P (x,y) <;> simp [supportRow,h]

/-- Explicit zero-product row interfaces suffice to make the two mixed supports cover.
The interfaces are precisely the Fubini consequences of the kernel zero integrals. -/
lemma pair_cover_of_strict_overlap
    (A B P L : Ω × Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hP : ∀ p, 0 ≤ P p)
    (hb : ∀ x z, 0 ≤ A (x,z)+B (x,z) ∧ A (x,z)+B (x,z) ≤ 1/2)
    (hr : ∀ᵐ u ∂μ, ∫ z, (A (u,z)+B (u,z)) ∂μ = (1:ℝ)/3)
    (hmissing : ∀ᵐ x ∂μ, ∀ᵐ u ∂μ, P (x,u)=0 →
      ∀ᵐ z ∂μ, A (x,z)*B (u,z)=0 ∧ B (x,z)*A (u,z)=0)
    (hsame : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ z ∂μ, A (x,z)*A (y,z)=0 ∧ B (x,z)*B (y,z)=0)
    (hstrict : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      (1:ℝ)/12 < ∫ z, (A (x,z)+B (x,z))*(A (y,z)+B (y,z)) ∂μ) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ u ∂μ, 0 < P (x,u) ∨ 0 < P (y,u) := by
  filter_upwards [hmissing,hsame,hstrict] with x hmx hsx htx
  filter_upwards [hmissing,hsx,htx] with y hmy hsxy htxy
  intro hL
  filter_upwards [hmx,hmy,hr] with u hx hy hu
  by_contra hn
  have hx0 : P (x,u)=0 := le_antisymm (le_of_not_gt (fun h => hn (Or.inl h))) (hP _)
  have hy0 : P (y,u)=0 := le_antisymm (le_of_not_gt (fun h => hn (Or.inr h))) (hP _)
  have hz : ∀ᵐ z ∂μ,
      A (x,z)*A (y,z)=0 ∧ B (x,z)*B (y,z)=0 ∧
      A (x,z)*B (u,z)=0 ∧ B (x,z)*A (u,z)=0 ∧
      A (y,z)*B (u,z)=0 ∧ B (y,z)*A (u,z)=0 := by
    filter_upwards [hsxy hL,hx hx0,hy hy0] with z hz hzx hzy
    exact ⟨hz.1,hz.2,hzx.1,hzx.2,hzy.1,hzy.2⟩
  have hh := overlap_bound_of_missing_row μ
    (fun z => A (x,z)) (fun z => B (x,z))
    (fun z => A (y,z)) (fun z => B (y,z))
    (fun z => A (u,z)) (fun z => B (u,z))
    (by
      intro g hg
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> fun_prop)
    (Filter.Eventually.of_forall (fun z => ⟨hb x z,hb y z,hb u z⟩)) hz hu
  exact (not_le_of_gt (htxy hL)) hh

/-- Cover, disjointness, and the independent-set upper bound give exact half rows.
Only positivity of the L-row integral is needed to select an eligible neighbor. -/
lemma half_rows_of_cover
    (P L : Ω × Ω → ℝ) (hm : Measurable P) (hL : ∀ p, 0 ≤ L p)
    (hdegree : ∀ᵐ x ∂μ, 0 < ∫ y, L (x,y) ∂μ)
    (hsmall : ∀ᵐ x ∂μ, (∫ y, supportRow P x y ∂μ) ≤ (1:ℝ)/2)
    (hcover : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ u ∂μ, 0 < P (x,u) ∨ 0 < P (y,u))
    (hdisjoint : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ u ∂μ, ¬ (0 < P (x,u) ∧ 0 < P (y,u))) :
    ∀ᵐ x ∂μ, μ {y | 0 < P (x,y)} = (1:ENNReal)/2 := by
  classical
  filter_upwards [hdegree,hsmall,hcover,hdisjoint] with x hx hs hc hd
  have hf : ∃ᶠ y in ae μ, 0 < L (x,y) := by
    by_contra hn
    have hzero : (fun y => L (x,y)) =ᵐ[μ] (fun _ => (0:ℝ)) := by
      filter_upwards [Filter.not_frequently.mp hn] with y hy
      exact le_antisymm (le_of_not_gt hy) (hL _)
    rw [integral_congr_ae hzero] at hx
    simp at hx
  obtain ⟨y,hy,hsy,hcy,hdy⟩ := (hf.and_eventually (hsmall.and (hc.and hd))).exists
  have he : (fun u => supportRow P x u+supportRow P y u) =ᵐ[μ] (fun _ => (1:ℝ)) := by
    filter_upwards [hcy hy,hdy hy] with u hcu hdu
    by_cases hxu : 0 < P (x,u)
    · have hyu : ¬ 0 < P (y,u) := fun h => hdu ⟨hxu,h⟩
      simp [supportRow,hxu,hyu]
    · have hyu := hcu.resolve_left hxu
      simp [supportRow,hxu,hyu]
  have hi (z : Ω) : Integrable (supportRow P z) μ :=
    unit_integrable μ _ (supportRow_measurable P hm z) (supportRow_bounds P z)
  have hsum : (∫ u, supportRow P x u ∂μ)+(∫ u, supportRow P y u ∂μ)=1 := by
    rw [← integral_add (hi x) (hi y),integral_congr_ae he]
    simp
  have heq : (∫ u, supportRow P x u ∂μ)=(1:ℝ)/2 := by linarith
  have hset : MeasurableSet {y | 0 < P (x,y)} :=
    measurableSet_lt measurable_const (hm.comp (measurable_const.prodMk measurable_id))
  have hreal : (μ {y | 0 < P (x,y)}).toReal = (1:ℝ)/2 := by
    change μ.real {y | 0 < P (x,y)} = (1:ℝ)/2
    rw [← integral_indicator_one hset]
    exact heq
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
  simpa using hreal

end TwoPairHalfSupport
namespace TwoPairHalfSupport
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma weighted_first (L : Ω × Ω → ℝ) (hm : Measurable L)
    (hb : ∀ p, 0 ≤ L p ∧ L p ≤ 1)
    (s : Ω → ℝ) (hs : Measurable s) (bs : ∀ x, 0 ≤ s x ∧ s x ≤ 1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, L (x,y) ∂μ=d) :
    (∫ p, s p.1*L p ∂μ.prod μ)=d*∫ x, s x ∂μ := by
  have hi : Integrable (fun p : Ω × Ω => s p.1*L p) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bs _) (hb _))
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, s x*d ∂μ := by
      apply integral_congr_ae
      filter_upwards [hr] with x hx
      rw [integral_const_mul,hx]
    _ = _ := by rw [integral_mul_const]; ring

lemma independent_indicator_le_half
    (L : Ω × Ω → ℝ) (hm : Measurable L)
    (hb : ∀ p, 0 ≤ L p ∧ L p ≤ 1)
    (hsymm : ∀ x y, L (x,y)=L (y,x))
    (d : ℝ) (hd : 0 < d) (hr : ∀ᵐ x ∂μ, ∫ y, L (x,y) ∂μ=d)
    (s : Ω → ℝ) (hs : Measurable s) (bs : ∀ x, s x=0 ∨ s x=1)
    (hind : ∀ᵐ p ∂μ.prod μ, s p.1=1 → s p.2=1 → L p=0) :
    (∫ x, s x ∂μ) ≤ (1:ℝ)/2 := by
  have bunit (x : Ω) : 0 ≤ s x ∧ s x ≤ 1 := by rcases bs x with h | h <;> simp [h]
  have hi1 : Integrable (fun p : Ω × Ω => s p.1*L p) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bunit _) (hb _))
  have hi2 : Integrable (fun p : Ω × Ω => s p.2*L p) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bunit _) (hb _))
  have hiL : Integrable L (μ.prod μ) := unit_integrable _ _ hm hb
  have h1 := weighted_first μ L hm hb s hs bunit d hr
  have h2 : (∫ p, s p.2*L p ∂μ.prod μ)=d*∫ x, s x ∂μ := by
    calc
      _ = ∫ p : Ω × Ω, s p.1*L (p.2,p.1) ∂μ.prod μ :=
        (integral_prod_swap (fun p : Ω × Ω => s p.2*L p)).symm
      _ = ∫ p : Ω × Ω, s p.1*L p ∂μ.prod μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun p => by dsimp only; rw [hsymm p.2 p.1])
      _ = _ := h1
  have htotal : (∫ p, L p ∂μ.prod μ)=d := by
    rw [integral_prod _ hiL,integral_congr_ae hr]
    simp
  have hle : ∀ᵐ p ∂μ.prod μ, s p.1*L p+s p.2*L p ≤ L p := by
    filter_upwards [hind] with p hp
    rcases bs p.1 with h | h <;> rcases bs p.2 with k | k
    · simpa [h,k] using (hb p).1
    · simp [h,k]
    · simp [h,k]
    · simp [h,k,hp h k]
  have hh := integral_mono_ae (hi1.add hi2) hiL hle
  change (∫ p : Ω × Ω, s p.1*L p+s p.2*L p ∂μ.prod μ) ≤ (∫ p, L p ∂μ.prod μ) at hh
  rw [integral_add hi1 hi2,h1,h2,htotal] at hh
  nlinarith

end TwoPairHalfSupport
namespace TwoPairHalfSupport
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Exact half-support saturation. The row-zero and independence hypotheses are
explicit almost-everywhere Fubini interfaces, not support-mass assumptions. -/
theorem half_support
    (A B P L : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hP : Measurable P) (hL : Measurable L)
    (bP : ∀ p, 0 ≤ P p) (bL : ∀ p, 0 ≤ L p ∧ L p ≤ 1)
    (sL : ∀ x y, L (x,y)=L (y,x))
    (bQ : ∀ x z, 0 ≤ A (x,z)+B (x,z) ∧ A (x,z)+B (x,z) ≤ 1/2)
    (rQ : ∀ᵐ u ∂μ, ∫ z, (A (u,z)+B (u,z)) ∂μ = (1:ℝ)/3)
    (d : ℝ) (hd : 0 < d) (rL : ∀ᵐ x ∂μ, ∫ y, L (x,y) ∂μ=d)
    (hmissing : ∀ᵐ x ∂μ, ∀ᵐ u ∂μ, P (x,u)=0 →
      ∀ᵐ z ∂μ, A (x,z)*B (u,z)=0 ∧ B (x,z)*A (u,z)=0)
    (hsame : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ z ∂μ, A (x,z)*A (y,z)=0 ∧ B (x,z)*B (y,z)=0)
    (hstrict : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      (1:ℝ)/12 < ∫ z, (A (x,z)+B (x,z))*(A (y,z)+B (y,z)) ∂μ)
    (hind : ∀ᵐ x ∂μ, ∀ᵐ p ∂μ.prod μ,
      0 < P (x,p.1) → 0 < P (x,p.2) → L p=0)
    (hdisjoint : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ u ∂μ, ¬ (0 < P (x,u) ∧ 0 < P (y,u))) :
    ∀ᵐ x ∂μ, μ {y | 0 < P (x,y)} = (1:ENNReal)/2 := by
  have hsmall : ∀ᵐ x ∂μ, (∫ y, supportRow P x y ∂μ) ≤ (1:ℝ)/2 := by
    filter_upwards [hind] with x hx
    apply independent_indicator_le_half μ L hL bL sL d hd rL
      (supportRow P x) (supportRow_measurable P hP x)
    · intro y
      by_cases hy : 0 < P (x,y) <;> simp [supportRow,hy]
    · filter_upwards [hx] with p hp
      intro h1 h2
      have hp1 : 0 < P (x,p.1) := by
        by_contra hn
        simp [supportRow,hn] at h1
      have hp2 : 0 < P (x,p.2) := by
        by_contra hn
        simp [supportRow,hn] at h2
      exact hp hp1 hp2
  apply half_rows_of_cover μ P L hP (fun p => (bL p).1)
    (rL.mono (fun x hx => by rw [hx]; exact hd)) hsmall
  · exact pair_cover_of_strict_overlap μ A B P L hA hB bP bQ rQ hmissing hsame hstrict
  · exact hdisjoint
end TwoPairHalfSupport
end


-- Local module: TwoPairCompositionAlgebra
section
open MeasureTheory
namespace TwoPairCompositionAlgebra
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma comp_assoc (f g h : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) (p : Ω × Ω) :
    comp μ (comp μ f g) h p = comp μ f (comp μ g h) p := by
  have hi : Integrable (fun q : Ω × Ω => f (p.1,q.1)*g q*h (q.2,p.2)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop)
      (fun q => mul_unit (mul_unit (bf (p.1,q.1)) (bg q)) (bh (q.2,p.2)))
  change (∫ z, (∫ w, f (p.1,w)*g (w,z) ∂μ)*h (z,p.2) ∂μ) =
    ∫ w, f (p.1,w)*(∫ z, g (w,z)*h (z,p.2) ∂μ) ∂μ
  simp_rw [← integral_mul_const, ← integral_const_mul, ← mul_assoc]
  exact (integral_integral_swap hi).symm

lemma comp_add_left (f g h : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) (p : Ω × Ω) :
    comp μ (fun q => f q+g q) h p = comp μ f h p + comp μ g h p := by
  have hif : Integrable (fun z => f (p.1,z)*h (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bf (p.1,z)) (bh (z,p.2)))
  have hig : Integrable (fun z => g (p.1,z)*h (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bg (p.1,z)) (bh (z,p.2)))
  simp only [comp,add_mul]
  exact integral_add hif hig

lemma comp_add_right (f g h : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) (p : Ω × Ω) :
    comp μ f (fun q => g q+h q) p = comp μ f g p + comp μ f h p := by
  have hig : Integrable (fun z => f (p.1,z)*g (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bf (p.1,z)) (bg (z,p.2)))
  have hih : Integrable (fun z => f (p.1,z)*h (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bf (p.1,z)) (bh (z,p.2)))
  simp only [comp,mul_add]
  exact integral_add hig hih

lemma comp_scale_left (f g : Ω × Ω → ℝ) (a : ℝ) (p : Ω × Ω) :
    comp μ (fun q => a*f q) g p = a*comp μ f g p := by
  simp only [comp,mul_assoc,integral_const_mul]

lemma comp_scale_right (f g : Ω × Ω → ℝ) (a : ℝ) (p : Ω × Ω) :
    comp μ f (fun q => a*g q) p = a*comp μ f g p := by
  dsimp only [comp]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by ring)

end TwoPairCompositionAlgebra
end


-- Local module: TwoPairSandwich
section
open MeasureTheory
namespace TwoPairSandwich
open FourColorKernels TwoPairCompositionAlgebra
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def sandwich (F M G : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  ∫ q : Ω × Ω, F (p.1,q.1)*M q*G (q.2,p.2) ∂μ.prod μ

lemma sandwich_eq_comp (F M G : Ω × Ω → ℝ)
    (hF : Measurable F) (hM : Measurable M) (hG : Measurable G)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bM : ∀ p, 0 ≤ M p ∧ M p ≤ 1)
    (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1) (p : Ω × Ω) :
    sandwich μ F M G p=comp μ F (comp μ M G) p := by
  have hi : Integrable (fun q : Ω × Ω => F (p.1,q.1)*M q*G (q.2,p.2)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun q => mul_unit (mul_unit (bF _) (bM _)) (bG _))
  unfold sandwich
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change (∫ w, F (p.1,z)*M (z,w)*G (w,p.2) ∂μ)=F (p.1,z)*∫ w, M (z,w)*G (w,p.2) ∂μ
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by dsimp only; ring)

lemma weighted_second (M : Ω × Ω → ℝ) (hM : Measurable M)
    (bM : ∀ p, 0 ≤ M p ∧ M p ≤ 1) (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (m : ℝ)
    (hc : ∀ᵐ y ∂μ, ∫ x, M (x,y) ∂μ=m) :
    (∫ p : Ω × Ω, M p*f p.2 ∂μ.prod μ)=m*∫ y, f y ∂μ := by
  have hi : Integrable (fun p : Ω × Ω => M p*f p.2) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bM _) (bf _))
  rw [integral_prod_symm _ hi]
  calc
    _ = ∫ y, m*f y ∂μ := by
      apply integral_congr_ae
      filter_upwards [hc] with y hy
      rw [integral_mul_const,hy]
    _ = _ := integral_const_mul _ _

lemma affine_sandwich_row (R M : Ω × Ω → ℝ)
    (hR : Measurable R) (hM : Measurable M)
    (bR : ∀ p, 0 ≤ R p ∧ R p ≤ 1) (bM : ∀ p, 0 ≤ M p ∧ M p ≤ 1)
    (sR : ∀ x y, R (x,y)=R (y,x)) (m : ℝ)
    (rM : ∀ᵐ x ∂μ, ∫ y, M (x,y) ∂μ=m)
    (cM : ∀ᵐ y ∂μ, ∫ x, M (x,y) ∂μ=m)
    (x y : Ω) (rx : ∫ z, R (x,z) ∂μ=(1:ℝ)/3)
    (ry : ∫ z, R (y,z) ∂μ=(1:ℝ)/3) :
    sandwich μ (fun p => (1-R p)/2) M (fun p => (1-R p)/2) (x,y)=
      m/12+sandwich μ R M R (x,y)/4 := by
  have hiM : Integrable M (μ.prod μ) := unit_integrable _ _ hM bM
  have hiRM : Integrable (fun p : Ω × Ω => R (x,p.1)*M p) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bR _) (bM _))
  have hiMR : Integrable (fun p : Ω × Ω => M p*R (p.2,y)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bM _) (bR _))
  have hiRMR : Integrable (fun p : Ω × Ω => R (x,p.1)*M p*R (p.2,y)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (mul_unit (bR _) (bM _)) (bR _))
  have htot : (∫ p, M p ∂μ.prod μ)=m := by
    rw [integral_prod _ hiM,integral_congr_ae rM]
    simp
  have hleft : (∫ p : Ω × Ω, R (x,p.1)*M p ∂μ.prod μ)=m/3 := by
    rw [TwoPairHalfSupport.weighted_first μ M hM bM (fun z => R (x,z))
      (by fun_prop) (fun z => bR (x,z)) m rM,rx]
    ring
  have hright : (∫ p : Ω × Ω, M p*R (p.2,y) ∂μ.prod μ)=m/3 := by
    rw [weighted_second μ M hM bM (fun z => R (z,y))
      (by fun_prop) (fun z => bR (z,y)) m cM]
    have hcol : (∫ z, R (z,y) ∂μ)=(1:ℝ)/3 := by simpa only [sR y] using ry
    rw [hcol]
    ring
  calc
    _ = ∫ p : Ω × Ω, ((M p-R (x,p.1)*M p-M p*R (p.2,y))+
        R (x,p.1)*M p*R (p.2,y))/4 ∂μ.prod μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by dsimp only; ring)
    _ = _ := by
      rw [integral_div]
      have ha := integral_add ((hiM.sub hiRM).sub hiMR) hiRMR
      have hb := integral_sub (hiM.sub hiRM) hiMR
      have hc := integral_sub hiM hiRM
      dsimp only [Pi.sub_apply] at ha hb hc
      rw [ha,hb,hc,htot,hleft,hright]
      unfold sandwich
      ring

/-- The middle kernel need not be symmetric or commute with R. -/
theorem affine_sandwich_ae (R M : Ω × Ω → ℝ)
    (hR : Measurable R) (hM : Measurable M)
    (bR : ∀ p, 0 ≤ R p ∧ R p ≤ 1) (bM : ∀ p, 0 ≤ M p ∧ M p ≤ 1)
    (sR : ∀ x y, R (x,y)=R (y,x)) (m : ℝ)
    (rM : ∀ᵐ x ∂μ, ∫ y, M (x,y) ∂μ=m)
    (cM : ∀ᵐ y ∂μ, ∫ x, M (x,y) ∂μ=m)
    (rR : ∀ᵐ x ∂μ, ∫ y, R (x,y) ∂μ=(1:ℝ)/3) :
    ∀ᵐ p ∂μ.prod μ,
      comp μ (fun q => (1-R q)/2) (comp μ M (fun q => (1-R q)/2)) p =
        m/12+comp μ R (comp μ M R) p/4 := by
  have hQ : Measurable (fun q => (1-R q)/2) := by fun_prop
  have bQ (p : Ω × Ω) : 0 ≤ (1-R p)/2 ∧ (1-R p)/2 ≤ 1 := by
    constructor <;> linarith [(bR p).1,(bR p).2]
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [rR] with x hx
    filter_upwards [rR] with y hy
    have he := affine_sandwich_row μ R M hR hM bR bM sR m rM cM x y hx hy
    rw [sandwich_eq_comp μ _ M _ hQ hM hQ bQ bM bQ,
      sandwich_eq_comp μ R M R hR hM hR bR bM bR] at he
    exact he
  · exact measurableSet_eq_fun
      (measurable_comp μ _ _ hQ (measurable_comp μ M _ hM hQ))
      (measurable_const.add ((measurable_comp μ R _ hR
        (measurable_comp μ M R hM hR)).div_const 4))

theorem cd_sandwich_lower
    (R C D : Ω × Ω → ℝ) (hR : Measurable R) (hC : Measurable C) (hD : Measurable D)
    (bR : ∀ p, 0 ≤ R p ∧ R p ≤ 1) (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sR : ∀ x y, R (x,y)=R (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (rR : ∀ᵐ x ∂μ, ∫ y, R (x,y) ∂μ=(1:ℝ)/3)
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6) :
    ∀ᵐ p ∂μ.prod μ, (1:ℝ)/432 ≤
      comp μ (fun q => (1-R q)/2) (comp μ C (comp μ D (fun q => (1-R q)/2))) p := by
  have hM := measurable_comp μ C D hC hD
  have bM := comp_bounds μ C D hC hD bC bD
  have rM : ∀ᵐ x ∂μ, ∫ y, comp μ C D (x,y) ∂μ=(1:ℝ)/36 := by
    convert comp_row μ C D hC hD bC bD (1/6) (1/6) rC rD using 1 <;> norm_num
  have cM : ∀ᵐ y ∂μ, ∫ x, comp μ C D (x,y) ∂μ=(1:ℝ)/36 := by
    filter_upwards [comp_row μ D C hD hC bD bC (1/6) (1/6) rD rC] with y hy
    have he : (fun x => comp μ C D (x,y))=(fun x => comp μ D C (y,x)) := by
      funext x
      exact comp_swap μ C D sC sD x y
    rw [he]
    norm_num at hy ⊢
    exact hy
  have he := affine_sandwich_ae μ R (comp μ C D) hR hM bR bM sR (1/36) rM cM rR
  have hMR := measurable_comp μ (comp μ C D) R hM hR
  have bMR := comp_bounds μ (comp μ C D) R hM hR bM bR
  have hQ : Measurable (fun q => (1-R q)/2) := by fun_prop
  have bQ (p : Ω × Ω) : 0 ≤ (1-R p)/2 ∧ (1-R p)/2 ≤ 1 := by
    constructor <;> linarith [(bR p).1,(bR p).2]
  have hassoc : comp μ (comp μ C D) (fun q => (1-R q)/2)=
      comp μ C (comp μ D (fun q => (1-R q)/2)) := by
    funext p
    exact comp_assoc μ C D _ hC hD hQ bC bD bQ p
  filter_upwards [he] with p hp
  rw [hassoc] at hp
  have hn := (comp_bounds μ R (comp μ (comp μ C D) R) hR hMR bR bMR p).1
  linarith
end TwoPairSandwich
end


-- Local module: TwoPairTraceAlgebra
section
open MeasureTheory
namespace TwoPairTraceAlgebra
open FourColorKernels TwoPairCompositionAlgebra
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma comp_transpose (f g : Ω × Ω → ℝ) (p : Ω × Ω) :
    comp μ f g p = comp μ (fun q => g (q.2,q.1)) (fun q => f (q.2,q.1)) (p.2,p.1) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => mul_comm _ _)

lemma pairing_comp_left (f g h : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (bf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (bg : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) :
    (∫ p, comp μ f g p*h (p.2,p.1) ∂μ.prod μ) =
      ∫ p, f p*comp μ g h (p.2,p.1) ∂μ.prod μ := by
  have hfg := measurable_comp μ f g hf hg
  have bfg := comp_bounds μ f g hf hg bf bg
  have hgh := measurable_comp μ g h hg hh
  have bgh := comp_bounds μ g h hg hh bg bh
  rw [integral_prod _ (unit_integrable _ _ (by fun_prop)
    (fun p => mul_unit (bfg p) (bh (p.2,p.1)))),
    integral_prod _ (unit_integrable _ _ (by fun_prop)
    (fun p => mul_unit (bf p) (bgh (p.2,p.1))))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hi : Integrable (fun p : Ω × Ω => f (x,p.1)*g p*h (p.2,x)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop)
      (fun p => mul_unit (mul_unit (bf (x,p.1)) (bg p)) (bh (p.2,x)))
  change (∫ y, (∫ z, f (x,z)*g (z,y) ∂μ)*h (y,x) ∂μ) =
    ∫ z, f (x,z)*(∫ y, g (z,y)*h (y,x) ∂μ) ∂μ
  simp_rw [← integral_mul_const,← integral_const_mul,← mul_assoc]
  exact (integral_integral_swap hi).symm

lemma reverse_three (A B C : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x))
    (sB : ∀ x y, B (x,y)=B (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (p : Ω × Ω) :
    comp μ C (comp μ B A) (p.2,p.1)=comp μ A (comp μ B C) p := by
  rw [comp_transpose μ C (comp μ B A) (p.2,p.1)]
  have he : (fun q => comp μ B A (q.2,q.1))=comp μ A B := by
    funext q
    exact comp_swap μ B A sB sA q.2 q.1
  have hc : (fun q => C (q.2,q.1))=C := by
    funext q
    exact sC q.2 q.1
  rw [he,hc]
  exact comp_assoc μ A B C hA hB hC bA bB bC p

end TwoPairTraceAlgebra
end


-- Local module: LowSupportPaths
section

open MeasureTheory
namespace Submissions.E811LowSupport.Paths

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

end Submissions.E811LowSupport.Paths


end


-- Local module: LowSupportRepresentatives
section

open MeasureTheory
namespace Submissions.E811LowSupport.Representatives
open Submissions.E811LowSupport.Paths

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

end Submissions.E811LowSupport.Representatives

end


-- Local module: LowSupportCyclePath
section
open MeasureTheory
namespace LowSupportCyclePath
open Submissions.E811LowSupport.Paths Submissions.E811LowSupport.Representatives
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
open Submissions.E811LowSupport.Paths Submissions.E811LowSupport.Representatives
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
end


-- Local module: FourColorBlock
section

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
end


-- Local module: FourColorTwinBlock
section
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
end


-- Local module: TwoPairDoubledDisjoint
section
open MeasureTheory
namespace TwoPairDoubledDisjoint
open FourColorKernels TwoPairCompositionAlgebra TwoPairTraceAlgebra
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma unit_zero_iff (f : Ω → ℝ) (hm : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (∫ x, f x ∂μ)=0 ↔ ∀ᵐ x ∂μ, f x=0 :=
  integral_eq_zero_iff_of_nonneg (fun x => (hb x).1) (unit_integrable μ f hm hb)

lemma cycle_zero_iff (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    LowSupportCycle.cycleNested (μ := μ) W=0 ↔
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, ∀ᵐ w ∂μ,
      W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x)=0 := by
  unfold LowSupportCycle.cycleNested
  rw [unit_zero_iff μ (fun x => ∫ y, ∫ z, ∫ u, ∫ v, ∫ w, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x) ∂μ ∂μ ∂μ ∂μ ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with x
  rw [unit_zero_iff μ (fun y => ∫ z, ∫ u, ∫ v, ∫ w, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x) ∂μ ∂μ ∂μ ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with y
  rw [unit_zero_iff μ (fun z => ∫ u, ∫ v, ∫ w, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x) ∂μ ∂μ ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with z
  rw [unit_zero_iff μ (fun u => ∫ v, ∫ w, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x) ∂μ ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with u
  rw [unit_zero_iff μ (fun v => ∫ w, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x) ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with v
  rw [unit_zero_iff μ (fun w => W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x)) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]

lemma cycle_zero_mono (W V : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hV : ∀ i, Measurable (V i))
    (bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) (bV : ∀ i p, 0 ≤ V i p ∧ V i p ≤ 1)
    (hle : ∀ i p, W i p ≤ V i p)
    (hz : LowSupportCycle.cycleNested (μ := μ) V=0) :
    LowSupportCycle.cycleNested (μ := μ) W=0 := by
  apply (cycle_zero_iff μ W hW bW).mpr
  have he := (cycle_zero_iff μ V hV bV).mp hz
  filter_upwards [he] with x hx
  filter_upwards [hx] with y hy
  filter_upwards [hy] with z hz
  filter_upwards [hz] with u hu
  filter_upwards [hu] with v hv
  filter_upwards [hv] with w hw
  have hlo : 0 ≤ W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x) := by
    repeat' first | exact (bW _ _).1 | apply mul_nonneg
  have hhi : W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,v)*W 4 (v,w)*W 5 (w,x) ≤
      V 0 (x,y)*V 1 (y,z)*V 2 (z,u)*V 3 (u,v)*V 4 (v,w)*V 5 (w,x) := by
    gcongr <;> repeat' first | exact (bW _ _).1 | exact (bV _ _).1 | exact hle _ _ | apply mul_nonneg
  linarith

lemma cycle_pairing (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    LowSupportCycle.cycleNested (μ := μ) W =
      ∫ p, comp μ (W 0) (W 1) p *
        comp μ (W 2) (comp μ (W 3) (comp μ (W 4) (W 5))) (p.2,p.1) ∂μ.prod μ := by
  have h34 := measurable_comp μ (W 3) (W 4) (hm 3) (hm 4)
  have b34 := comp_bounds μ (W 3) (W 4) (hm 3) (hm 4) (hb 3) (hb 4)
  have h234 := measurable_comp μ (W 2) (comp μ (W 3) (W 4)) (hm 2) h34
  have b234 := comp_bounds μ (W 2) (comp μ (W 3) (W 4)) (hm 2) h34 (hb 2) b34
  have h01 := measurable_comp μ (W 0) (W 1) (hm 0) (hm 1)
  have b01 := comp_bounds μ (W 0) (W 1) (hm 0) (hm 1) (hb 0) (hb 1)
  rw [← LowSupportCyclePath.closing_eq_cycle_pointwise W hm hb]
  have hc : LowSupportCyclePath.closing (μ := μ) W =
      ∫ p, comp μ (comp μ (W 0) (W 1)) (comp μ (W 2) (comp μ (W 3) (W 4))) p * W 5 (p.2,p.1) ∂μ.prod μ := by
    simp only [LowSupportCyclePath.closing,Submissions.E811LowSupport.Paths.pathKernel]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    change comp μ (W 0) (comp μ (W 1) (comp μ (W 2) (comp μ (W 3) (W 4)))) p * _ = _
    dsimp only
    rw [comp_assoc μ (W 0) (W 1) _ (hm 0) (hm 1) h234 (hb 0) (hb 1) b234]
  rw [hc,pairing_comp_left μ _ _ _ h01 h234 (hm 5) b01 b234 (hb 5)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  rw [comp_assoc μ (W 2) (comp μ (W 3) (W 4)) (W 5) (hm 2) h34 (hm 5) (hb 2) b34 (hb 5)]
  have he : comp μ (comp μ (W 3) (W 4)) (W 5)=comp μ (W 3) (comp μ (W 4) (W 5)) := by
    funext q
    exact comp_assoc μ (W 3) (W 4) (W 5) (hm 3) (hm 4) (hm 5) (hb 3) (hb 4) (hb 5) q
  rw [he]

lemma min_sum_cycle_zero (A B C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (bQ : ∀ p, A p+B p ≤ 1)
    (z1 : LowSupportCycle.cycleNested (μ := μ) ![B,B,A,C,D,A]=0)
    (z2 : LowSupportCycle.cycleNested (μ := μ) ![A,B,A,C,D,B]=0)
    (z3 : LowSupportCycle.cycleNested (μ := μ) ![A,B,B,C,D,A]=0)
    (z4 : LowSupportCycle.cycleNested (μ := μ) ![A,A,B,C,D,B]=0) :
    LowSupportCycle.cycleNested (μ := μ)
      ![fun p => min (A p) (B p),fun p => min (A p) (B p),fun p => A p+B p,C,D,fun p => A p+B p]=0 := by
  let H := fun p => min (A p) (B p)
  have hH : Measurable H := hA.min hB
  have bH (p : Ω × Ω) : 0 ≤ H p ∧ H p ≤ 1 :=
    ⟨le_min (bA p).1 (bB p).1, (min_le_left _ _).trans (bA p).2⟩
  have hm (X Y : Ω × Ω → ℝ) (hx : Measurable X) (hy : Measurable Y) :
      ∀ i, Measurable (![H,H,X,C,D,Y] i) := by
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption
  have hb (X Y : Ω × Ω → ℝ) (bx : ∀ p, 0 ≤ X p ∧ X p ≤ 1)
      (byy : ∀ p, 0 ≤ Y p ∧ Y p ≤ 1) :
      ∀ i p, 0 ≤ (![H,H,X,C,D,Y] i) p ∧ (![H,H,X,C,D,Y] i) p ≤ 1 := by
    intro i p
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      first | exact bH p | exact bx p | exact byy p | exact bC p | exact bD p
  have e1 : LowSupportCycle.cycleNested (μ := μ) ![H,H,A,C,D,A]=0 := by
    apply cycle_zero_mono μ _ ![B,B,A,C,D,A] (hm A A hA hA)
      (by intro i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption)
      (hb A A bA bA)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact bA p | exact bB p | exact bC p | exact bD p)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact le_rfl | exact min_le_left _ _ | exact min_le_right _ _) z1
  have t1 := (cycle_zero_iff μ _ (hm A A hA hA) (hb A A bA bA)).mp e1
  have e2 : LowSupportCycle.cycleNested (μ := μ) ![H,H,A,C,D,B]=0 := by
    apply cycle_zero_mono μ _ ![A,B,A,C,D,B] (hm A B hA hB)
      (by intro i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption)
      (hb A B bA bB)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact bA p | exact bB p | exact bC p | exact bD p)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact le_rfl | exact min_le_left _ _ | exact min_le_right _ _) z2
  have t2 := (cycle_zero_iff μ _ (hm A B hA hB) (hb A B bA bB)).mp e2
  have e3 : LowSupportCycle.cycleNested (μ := μ) ![H,H,B,C,D,A]=0 := by
    apply cycle_zero_mono μ _ ![A,B,B,C,D,A] (hm B A hB hA)
      (by intro i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption)
      (hb B A bB bA)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact bA p | exact bB p | exact bC p | exact bD p)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact le_rfl | exact min_le_left _ _ | exact min_le_right _ _) z3
  have t3 := (cycle_zero_iff μ _ (hm B A hB hA) (hb B A bB bA)).mp e3
  have e4 : LowSupportCycle.cycleNested (μ := μ) ![H,H,B,C,D,B]=0 := by
    apply cycle_zero_mono μ _ ![A,A,B,C,D,B] (hm B B hB hB)
      (by intro i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption)
      (hb B B bB bB)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact bA p | exact bB p | exact bC p | exact bD p)
      (by intro i p; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact le_rfl | exact min_le_left _ _ | exact min_le_right _ _) z4
  have t4 := (cycle_zero_iff μ _ (hm B B hB hB) (hb B B bB bB)).mp e4
  have bsum (p : Ω × Ω) : 0 ≤ A p+B p ∧ A p+B p ≤ 1 := ⟨add_nonneg (bA p).1 (bB p).1,bQ p⟩
  apply (cycle_zero_iff μ _ (hm _ _ (hA.add hB) (hA.add hB)) (hb _ _ bsum bsum)).mpr
  filter_upwards [t1,t2,t3,t4] with x v0_1 v0_2 v0_3 v0_4
  filter_upwards [v0_1,v0_2,v0_3,v0_4] with y v1_1 v1_2 v1_3 v1_4
  filter_upwards [v1_1,v1_2,v1_3,v1_4] with z v2_1 v2_2 v2_3 v2_4
  filter_upwards [v2_1,v2_2,v2_3,v2_4] with u v3_1 v3_2 v3_3 v3_4
  filter_upwards [v3_1,v3_2,v3_3,v3_4] with v v4_1 v4_2 v4_3 v4_4
  filter_upwards [v4_1,v4_2,v4_3,v4_4] with w v5_1 v5_2 v5_3 v5_4
  change H (x,y)*H (y,z)*A (z,u)*C (u,v)*D (v,w)*A (w,x)=0 at v5_1
  change H (x,y)*H (y,z)*A (z,u)*C (u,v)*D (v,w)*B (w,x)=0 at v5_2
  change H (x,y)*H (y,z)*B (z,u)*C (u,v)*D (v,w)*A (w,x)=0 at v5_3
  change H (x,y)*H (y,z)*B (z,u)*C (u,v)*D (v,w)*B (w,x)=0 at v5_4
  change H (x,y)*H (y,z)*(A (z,u)+B (z,u))*C (u,v)*D (v,w)*(A (w,x)+B (w,x))=0
  linear_combination v5_1+v5_2+v5_3+v5_4


lemma square_zero_of_positive_pairing (H K : Ω × Ω → ℝ)
    (hH : Measurable H) (hK : Measurable K)
    (bH : ∀ p, 0 ≤ H p ∧ H p ≤ 1) (bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1)
    (sH : ∀ x y, H (x,y)=H (y,x))
    (hp : ∀ᵐ p ∂μ.prod μ, 0 < K p)
    (hz : (∫ p, comp μ H H p*K (p.2,p.1) ∂μ.prod μ)=0) :
    H =ᵐ[μ.prod μ] fun _ => 0 := by
  have hHH := measurable_comp μ H H hH hH
  have bHH := comp_bounds μ H H hH hH bH bH
  have hi := unit_integrable (μ.prod μ) (fun p => comp μ H H p*K (p.2,p.1))
    (by fun_prop) (fun p => mul_unit (bHH p) (bK _))
  have he := (integral_eq_zero_iff_of_nonneg
    (fun p => mul_nonneg (bHH p).1 (bK _).1) hi).mp hz
  have hhzero : comp μ H H =ᵐ[μ.prod μ] fun _ => 0 := by
    filter_upwards [he,Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp] with p he hp
    exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
  have hint : (∫ p, comp μ H H p ∂μ.prod μ)=0 := by
    rw [integral_congr_ae hhzero,integral_zero]
  have hsquare : (∫ z, (∫ x, H (x,z) ∂μ)^2 ∂μ)=0 := by
    have hh := FourColorTwinBlock.block_energy (μ := μ) Set.univ H hH bH sH
    simp only [Measure.restrict_univ,FourColorTwinBlock.flux] at hh
    exact hh.symm.trans hint
  have hf : Measurable (fun z => ∫ x, H (x,z) ∂μ) := by fun_prop
  have bf (z : Ω) : 0 ≤ (∫ x, H (x,z) ∂μ) ∧ (∫ x, H (x,z) ∂μ) ≤ 1 :=
    LowSupportAnalysis.integral_unit_bounds (by fun_prop) (fun x => bH (x,z))
  have hfzero : (fun z => ∫ x, H (x,z) ∂μ) =ᵐ[μ] fun _ => 0 := by
    have he := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _)
      (unit_integrable μ _ (hf.pow_const 2) (fun z => by simpa [pow_two] using mul_unit (bf z) (bf z)))).mp hsquare
    filter_upwards [he] with z hz
    exact sq_eq_zero_iff.mp hz
  have htotal : (∫ p, H p ∂μ.prod μ)=0 := by
    rw [integral_prod_symm _ (unit_integrable _ H hH bH),integral_congr_ae hfzero,integral_zero]
  exact (integral_eq_zero_iff_of_nonneg (fun p => (bH p).1)
    (unit_integrable _ H hH bH)).mp htotal

theorem doubled_disjoint (A B C D R : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D) (hR : Measurable R)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (bR : ∀ p, 0 ≤ R p ∧ R p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (sR : ∀ x y, R (x,y)=R (y,x))
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6)
    (rR : ∀ᵐ x ∂μ, ∫ y, R (x,y) ∂μ=(1:ℝ)/3)
    (eQ : ∀ p, A p+B p=(1-R p)/2)
    (z1 : LowSupportCycle.cycleNested (μ := μ) ![B,B,A,C,D,A]=0)
    (z2 : LowSupportCycle.cycleNested (μ := μ) ![A,B,A,C,D,B]=0)
    (z3 : LowSupportCycle.cycleNested (μ := μ) ![A,B,B,C,D,A]=0)
    (z4 : LowSupportCycle.cycleNested (μ := μ) ![A,A,B,C,D,B]=0) :
    ∀ᵐ p ∂μ.prod μ, A p*B p=0 := by
  let H := fun p => min (A p) (B p)
  let Q := fun p => A p+B p
  have hH : Measurable H := hA.min hB
  have bH (p : Ω × Ω) : 0 ≤ H p ∧ H p ≤ 1 :=
    ⟨le_min (bA p).1 (bB p).1,(min_le_left _ _).trans (bA p).2⟩
  have sH (x y : Ω) : H (x,y)=H (y,x) := by dsimp [H]; rw [sA x y,sB x y]
  have hQ : Measurable Q := hA.add hB
  have bQ (p : Ω × Ω) : 0 ≤ Q p ∧ Q p ≤ 1 := by
    dsimp [Q]
    rw [eQ p]
    constructor <;> linarith [(bR p).1,(bR p).2]
  have hDQ := measurable_comp μ D Q hD hQ
  have bDQ := comp_bounds μ D Q hD hQ bD bQ
  have hCDQ := measurable_comp μ C (comp μ D Q) hC hDQ
  have bCDQ := comp_bounds μ C (comp μ D Q) hC hDQ bC bDQ
  have hK := measurable_comp μ Q (comp μ C (comp μ D Q)) hQ hCDQ
  have bK := comp_bounds μ Q (comp μ C (comp μ D Q)) hQ hCDQ bQ bCDQ
  have qeq : Q=(fun p => (1-R p)/2) := funext eQ
  have hp : ∀ᵐ p ∂μ.prod μ, 0 < comp μ Q (comp μ C (comp μ D Q)) p := by
    rw [qeq]
    filter_upwards [TwoPairSandwich.cd_sandwich_lower μ R C D hR hC hD bR bC bD sR sC sD rR rC rD] with p hp
    linarith
  have hz := min_sum_cycle_zero μ A B C D hA hB hC hD bA bB bC bD (fun p => (bQ p).2) z1 z2 z3 z4
  have hm : ∀ i, Measurable (![H,H,Q,C,D,Q] i) := by
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption
  have hb : ∀ i p, 0 ≤ (![H,H,Q,C,D,Q] i) p ∧ (![H,H,Q,C,D,Q] i) p ≤ 1 := by
    intro i p
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      first | exact bH p | exact bQ p | exact bC p | exact bD p
  have hpair := cycle_pairing μ ![H,H,Q,C,D,Q] hm hb
  have hzero : (∫ p, comp μ H H p*comp μ Q (comp μ C (comp μ D Q)) (p.2,p.1) ∂μ.prod μ)=0 := by
    exact hpair.symm.trans hz
  have hh := square_zero_of_positive_pairing μ H _ hH hK bH bK sH hp hzero
  filter_upwards [hh] with p hp
  dsimp [H] at hp
  rcases le_total (A p) (B p) with hab | hba
  · rw [min_eq_left hab] at hp
    rw [hp,zero_mul]
  · rw [min_eq_right hba] at hp
    rw [hp,mul_zero]

end TwoPairDoubledDisjoint

end


-- Local module: TwoPairCompositionZeros
section
open MeasureTheory
namespace TwoPairCompositionZeros
open FourColorKernels TwoPairCompositionAlgebra TwoPairTraceAlgebra TwoPairDoubledDisjoint
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma comp_four_add (F G H I : Ω × Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) (hI : Measurable I)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (bH : ∀ p, 0 ≤ H p ∧ H p ≤ 1) (bI : ∀ p, 0 ≤ I p ∧ I p ≤ 1) (p : Ω × Ω) :
    comp μ (fun q => F q+G q) (fun q => H q+I q) p =
      comp μ F H p+comp μ F I p+comp μ G H p+comp μ G I p := by
  have iFH : Integrable (fun z => F (p.1,z)*H (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bF _) (bH _))
  have iFI : Integrable (fun z => F (p.1,z)*I (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bF _) (bI _))
  have iGH : Integrable (fun z => G (p.1,z)*H (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bG _) (bH _))
  have iGI : Integrable (fun z => G (p.1,z)*I (z,p.2)) μ :=
    unit_integrable _ _ (by fun_prop) (fun z => mul_unit (bG _) (bI _))
  change (∫ z, (F (p.1,z)+G (p.1,z))*(H (z,p.2)+I (z,p.2)) ∂μ)=_
  calc
    _ = ∫ z, ((F (p.1,z)*H (z,p.2)+F (p.1,z)*I (z,p.2))+G (p.1,z)*H (z,p.2))+G (p.1,z)*I (z,p.2) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ = _ := by
      have ha := integral_add ((iFH.add iFI).add iGH) iGI
      have hb := integral_add (iFH.add iFI) iGH
      have hc := integral_add iFH iFI
      dsimp only [Pi.add_apply] at ha hb hc
      rw [ha,hb,hc]
      rfl

lemma cycle_four_path_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i x y, W i (x,y)=W i (y,x))
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ p ∂μ.prod μ, comp μ (W 0) (W 1) p *
      comp μ (comp μ (W 5) (W 4)) (comp μ (W 3) (W 2)) p=0 := by
  have h23 := measurable_comp μ (W 2) (W 3) (hm 2) (hm 3)
  have b23 := comp_bounds μ (W 2) (W 3) (hm 2) (hm 3) (hb 2) (hb 3)
  have h45 := measurable_comp μ (W 4) (W 5) (hm 4) (hm 5)
  have b45 := comp_bounds μ (W 4) (W 5) (hm 4) (hm 5) (hb 4) (hb 5)
  have h54 := measurable_comp μ (W 5) (W 4) (hm 5) (hm 4)
  have b54 := comp_bounds μ (W 5) (W 4) (hm 5) (hm 4) (hb 5) (hb 4)
  have h32 := measurable_comp μ (W 3) (W 2) (hm 3) (hm 2)
  have b32 := comp_bounds μ (W 3) (W 2) (hm 3) (hm 2) (hb 3) (hb 2)
  have hK := measurable_comp μ (comp μ (W 5) (W 4)) (comp μ (W 3) (W 2)) h54 h32
  have bK := comp_bounds μ (comp μ (W 5) (W 4)) (comp μ (W 3) (W 2)) h54 h32 b54 b32
  have h01 := measurable_comp μ (W 0) (W 1) (hm 0) (hm 1)
  have b01 := comp_bounds μ (W 0) (W 1) (hm 0) (hm 1) (hb 0) (hb 1)
  have he (p : Ω × Ω) :
      comp μ (W 2) (comp μ (W 3) (comp μ (W 4) (W 5))) (p.2,p.1)=
        comp μ (comp μ (W 5) (W 4)) (comp μ (W 3) (W 2)) p := by
    rw [← comp_assoc μ (W 2) (W 3) (comp μ (W 4) (W 5))
      (hm 2) (hm 3) h45 (hb 2) (hb 3) b45]
    rw [comp_transpose μ (comp μ (W 2) (W 3)) (comp μ (W 4) (W 5))]
    have ht1 : (fun q => comp μ (W 4) (W 5) (q.2,q.1))=comp μ (W 5) (W 4) := by
      funext q
      exact comp_swap μ _ _ (hs 4) (hs 5) q.2 q.1
    have ht2 : (fun q => comp μ (W 2) (W 3) (q.2,q.1))=comp μ (W 3) (W 2) := by
      funext q
      exact comp_swap μ _ _ (hs 2) (hs 3) q.2 q.1
    rw [ht1,ht2]
  have hzint : (∫ p, comp μ (W 0) (W 1) p *
      comp μ (comp μ (W 5) (W 4)) (comp μ (W 3) (W 2)) p ∂μ.prod μ)=0 := by
    have hc := (cycle_pairing μ W hm hb).symm.trans hz
    simpa only [he] using hc
  exact (integral_eq_zero_iff_of_nonneg (fun p => mul_nonneg (b01 p).1 (bK p).1)
    (unit_integrable _ _ (h01.mul hK) (fun p => mul_unit (b01 p) (bK p)))).mp hzint

/-- Eight explicit balanced six-cycle words suffice; no degree hypothesis is used. -/
theorem mixed_square_zero (A B C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (hz : ∀ t a b : Bool, LowSupportCycle.cycleNested (μ := μ)
      ![if t then C else D,if t then D else C,
        if b then B else A,if b then A else B,
        if a then B else A,if a then A else B]=0) :
    ∀ᵐ p ∂μ.prod μ,
      comp μ (fun q => comp μ A B q+comp μ B A q)
        (fun q => comp μ A B q+comp μ B A q) p *
      (comp μ C D p+comp μ D C p)=0 := by
  have hAB := measurable_comp μ A B hA hB
  have bAB := comp_bounds μ A B hA hB bA bB
  have hBA := measurable_comp μ B A hB hA
  have bBA := comp_bounds μ B A hB hA bB bA
  have he (t a b : Bool) : ∀ᵐ p ∂μ.prod μ,
      comp μ (if t then C else D) (if t then D else C) p *
      comp μ (comp μ (if a then A else B) (if a then B else A))
        (comp μ (if b then A else B) (if b then B else A)) p=0 := by
    have hm : ∀ i, Measurable
        (![if t then C else D,if t then D else C,if b then B else A,if b then A else B,
           if a then B else A,if a then A else B] i) := by
      intro i
      cases t <;> cases a <;> cases b <;> fin_cases i <;> simp only [Bool.false_eq_true, ↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption
    have hb : ∀ i p, 0 ≤ (![if t then C else D,if t then D else C,if b then B else A,if b then A else B,
           if a then B else A,if a then A else B] i) p ∧
        (![if t then C else D,if t then D else C,if b then B else A,if b then A else B,
           if a then B else A,if a then A else B] i) p ≤ 1 := by
      intro i p
      cases t <;> cases a <;> cases b <;> fin_cases i <;> simp only [Bool.false_eq_true, ↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact bA p | exact bB p | exact bC p | exact bD p
    have hs : ∀ i x y, (![if t then C else D,if t then D else C,if b then B else A,if b then A else B,
           if a then B else A,if a then A else B] i) (x,y)=
        (![if t then C else D,if t then D else C,if b then B else A,if b then A else B,
           if a then B else A,if a then A else B] i) (y,x) := by
      intro i x y
      cases t <;> cases a <;> cases b <;> fin_cases i <;> simp only [Bool.false_eq_true, ↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
        first | exact sA x y | exact sB x y | exact sC x y | exact sD x y
    exact cycle_four_path_zero μ _ hm hb hs (hz t a b)
  filter_upwards [he true true true,he true true false,he true false true,he true false false,
    he false true true,he false true false,he false false true,he false false false]
    with p h1 h2 h3 h4 h5 h6 h7 h8
  simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 h3 h4 h5 h6 h7 h8
  rw [comp_four_add μ (comp μ A B) (comp μ B A) (comp μ A B) (comp μ B A)
    hAB hBA hAB hBA bAB bBA bAB bBA p]
  linear_combination h1+h2+h3+h4+h5+h6+h7+h8
end TwoPairCompositionZeros
end


-- Local module: TwoPairHalfTransport
section
open MeasureTheory
namespace TwoPairHalfTransport
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Disjoint capped images with total mass equal to the cap exhaust it. -/
lemma disjoint_images_saturate (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (d : ℝ) (hd : 0 < d)
    (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ x, 0 ≤ f x ∧ f x ≤ d)
    (bg : ∀ x, 0 ≤ g x ∧ g x ≤ d)
    (hz : ∀ᵐ x ∂μ, f x * g x = 0)
    (hrf : (∫ x, f x ∂μ) = d/2)
    (hrg : (∫ x, g x ∂μ) = d/2) :
    ∃ U : Set Ω, MeasurableSet U ∧ μ U = (1 : ENNReal)/2 ∧
      f =ᵐ[μ] U.indicator (fun _ => d) ∧
      g =ᵐ[μ] Uᶜ.indicator (fun _ => d) := by
  classical
  have hi (h : Ω → ℝ) (hm : Measurable h) (hb : ∀ x, 0 ≤ h x ∧ h x ≤ d) :
      Integrable h μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable d
    exact Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2)
  have hif := hi f hf bf
  have hig := hi g hg bg
  have hle : ∀ᵐ x ∂μ, f x + g x ≤ d := by
    filter_upwards [hz] with x hx
    rcases mul_eq_zero.mp hx with hx | hx
    · simpa [hx] using (bg x).2
    · simpa [hx] using (bf x).2
  have he : (fun x => f x + g x) =ᵐ[μ] fun _ => d := by
    apply (integral_eq_iff_of_ae_le (hif.add hig) (integrable_const d) hle).mp
    change (∫ x, f x + g x ∂μ) = ∫ x, d ∂μ
    rw [integral_add hif hig, hrf, hrg]
    simp
  let U : Set Ω := {x | 0 < f x}
  have hU : MeasurableSet U := measurableSet_lt measurable_const hf
  have hfe : f =ᵐ[μ] U.indicator (fun _ => d) := by
    filter_upwards [hz,he] with x hx hs
    by_cases hu : x ∈ U
    · have hp : 0 < f x := hu
      have hg0 : g x = 0 := (mul_eq_zero.mp hx).resolve_left (ne_of_gt hp)
      simp only [hg0, add_zero] at hs
      simpa [Set.indicator_of_mem hu] using hs
    · have hf0 : f x = 0 := le_antisymm (le_of_not_gt hu) (bf x).1
      simp [Set.indicator_of_notMem hu,hf0]
  have hge : g =ᵐ[μ] Uᶜ.indicator (fun _ => d) := by
    filter_upwards [hfe,he] with x hx hs
    by_cases hu : x ∈ U
    · have hfval : f x = d := by simpa [Set.indicator_of_mem hu] using hx
      have hg0 : g x = 0 := by linarith
      simp [hu,hg0]
    · have hf0 : f x = 0 := by simpa [Set.indicator_of_notMem hu] using hx
      have hgval : g x = d := by linarith
      simp [hu,hgval]
  have hmass : μ U = (1 : ENNReal)/2 := by
    have hiU := integral_congr_ae hfe
    rw [hrf,integral_indicator_const d hU] at hiU
    have hm : μ.real U = (1 : ℝ)/2 := by
      simp only [smul_eq_mul] at hiU
      nlinarith
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ U) (by simp)).mp
    simpa [measureReal_def] using hm
  exact ⟨U,hU,hmass,hfe,hge⟩

lemma disjoint_images_saturate_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (d : ℝ) (hd : 0 < d)
    (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ d)
    (bg : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ d)
    (hz : ∀ᵐ x ∂μ, f x * g x = 0)
    (hrf : (∫ x, f x ∂μ) = d/2)
    (hrg : (∫ x, g x ∂μ) = d/2) :
    ∃ U : Set Ω, MeasurableSet U ∧ μ U = (1 : ENNReal)/2 ∧
      f =ᵐ[μ] U.indicator (fun _ => d) ∧
      g =ᵐ[μ] Uᶜ.indicator (fun _ => d) := by
  let fc : Ω → ℝ := fun x => max 0 (min d (f x))
  let gc : Ω → ℝ := fun x => max 0 (min d (g x))
  have ef : fc =ᵐ[μ] f := by
    filter_upwards [bf] with x hx
    simp [fc,min_eq_right hx.2,max_eq_right hx.1]
  have eg : gc =ᵐ[μ] g := by
    filter_upwards [bg] with x hx
    simp [gc,min_eq_right hx.2,max_eq_right hx.1]
  have cb (h : Ω → ℝ) (x : Ω) :
      0 ≤ max 0 (min d (h x)) ∧ max 0 (min d (h x)) ≤ d :=
    ⟨le_max_left _ _,max_le hd.le (min_le_left _ _)⟩
  obtain ⟨U,hU,hm,hfu,hgu⟩ := disjoint_images_saturate μ fc gc d hd
    (by dsimp [fc]; fun_prop) (by dsimp [gc]; fun_prop)
    (cb f) (cb g) (by filter_upwards [ef,eg,hz] with x hx hy hz; simpa [hx,hy] using hz)
    ((integral_congr_ae ef).trans hrf) ((integral_congr_ae eg).trans hrg)
  exact ⟨U,hU,hm,ef.symm.trans hfu,eg.symm.trans hgu⟩

end TwoPairHalfTransport

end


-- Local module: TwoPairHalfSetOperator
section
open MeasureTheory
namespace TwoPairHalfSetOperator
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def act (C : Ω × Ω → ℝ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  ∫ y, C (x,y)*f y ∂μ

noncomputable def oneSet (S : Set Ω) : Ω → ℝ := S.indicator (fun _ => 1)

lemma oneSet_measurable (S : Set Ω) (hS : MeasurableSet S) : Measurable (oneSet S) :=
  measurable_const.indicator hS
lemma oneSet_binary (S : Set Ω) (x : Ω) : oneSet S x=0 ∨ oneSet S x=1 := by
  classical
  by_cases hx : x ∈ S <;> simp [oneSet,hx]
lemma oneSet_bounds (S : Set Ω) (x : Ω) : 0 ≤ oneSet S x ∧ oneSet S x ≤ 1 := by
  rcases oneSet_binary S x with h | h <;> simp [h]

lemma measurable_act (C : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hC : Measurable C) (hf : Measurable f) : Measurable (act μ C f) := by
  exact ((hC.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right').measurable

lemma act_bounds (C : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hC : Measurable C) (hf : Measurable f)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : Ω) :
    0 ≤ act μ C f x ∧ act μ C f x ≤ 1 := by
  constructor
  · exact integral_nonneg (fun y => mul_nonneg (bC _).1 (bf _).1)
  · have hi := unit_integrable μ (fun y => C (x,y)*f y) (by fun_prop)
      (fun y => mul_unit (bC _) (bf _))
    have hh := integral_mono hi (integrable_const (1:ℝ)) (fun y => (mul_unit (bC _) (bf _)).2)
    simpa [act] using hh

lemma act_le_row (C : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hC : Measurable C) (hf : Measurable f)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : Ω) :
    act μ C f x ≤ ∫ y, C (x,y) ∂μ := by
  apply integral_mono
    (unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bC _) (bf _)))
    (unit_integrable μ _ (by fun_prop) (fun y => bC (x,y)))
  intro y
  exact mul_le_of_le_one_right (bC (x,y)).1 (bf y).2

lemma act_total (C : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hC : Measurable C) (hf : Measurable f)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (d : ℝ)
    (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d) :
    (∫ x, act μ C f x ∂μ)=d*∫ x, f x ∂μ := by
  have hi : Integrable (fun p : Ω × Ω => C p*f p.2) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bC _) (bf _))
  unfold act
  rw [integral_integral_swap hi]
  calc
    _ = ∫ y, d*f y ∂μ := by
      apply integral_congr_ae
      filter_upwards [hr] with y hy
      rw [integral_mul_const]
      have he : (∫ x, C (x,y) ∂μ)=d := by simpa only [sC y] using hy
      rw [he]
    _ = _ := integral_const_mul _ _

lemma act_pairing (C : Ω × Ω → ℝ) (f g : Ω → ℝ)
    (hC : Measurable C) (hf : Measurable f) (hg : Measurable g)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (bg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) :
    (∫ x, f x*act μ C g x ∂μ)=(∫ x, g x*act μ C f x ∂μ) := by
  have hi : Integrable (fun p : Ω × Ω => f p.1*(C p*g p.2)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bf _) (mul_unit (bC _) (bg _)))
  calc
    _ = ∫ x, ∫ y, f x*(C (x,y)*g y) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (integral_const_mul _ _).symm)
    _ = ∫ y, ∫ x, f x*(C (x,y)*g y) ∂μ ∂μ := integral_integral_swap hi
    _ = ∫ y, g y*act μ C f y ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∫ x, f x*(C (x,y)*g y) ∂μ)=g y*∫ x, C (y,x)*f x ∂μ
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [sC x y]; ring)

lemma recover_capped_indicator (f s : Ω → ℝ) (hf : Measurable f) (hs : Measurable s)
    (d : ℝ) (hd : 0 < d) (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ d)
    (bs : ∀ x, s x=0 ∨ s x=1) (hmass : ∫ x, s x ∂μ=(1:ℝ)/2)
    (ht : ∫ x, f x ∂μ=d/2) (hp : ∫ x, s x*f x ∂μ=d/2) :
    f =ᵐ[μ] (fun x => d*s x) := by
  have hif : Integrable f μ := by
    apply Integrable.of_bound hf.aestronglyMeasurable d
    filter_upwards [bf] with x hx
    simpa [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have bis (x : Ω) : 0 ≤ s x ∧ s x ≤ 1 := by rcases bs x with h | h <;> simp [h]
  have his : Integrable s μ := unit_integrable μ s hs bis
  have hip : Integrable (fun x => s x*f x) μ := by
    apply Integrable.of_bound (by fun_prop) d
    filter_upwards [bf] with x hx
    rcases bs x with h | h <;> simp [h,Real.norm_eq_abs,abs_of_nonneg hx.1] <;> linarith
  have hle1 : ∀ᵐ x ∂μ, s x*f x ≤ f x := by
    filter_upwards [bf] with x hx
    exact mul_le_of_le_one_left hx.1 (bis x).2
  have he1 : (fun x => s x*f x) =ᵐ[μ] f :=
    (integral_eq_iff_of_ae_le hip hif hle1).mp (by rw [hp,ht])
  have hle2 : ∀ᵐ x ∂μ, s x*f x ≤ d*s x := by
    filter_upwards [bf] with x hx
    nlinarith [mul_le_mul_of_nonneg_left hx.2 (bis x).1]
  have he2 : (fun x => s x*f x) =ᵐ[μ] (fun x => d*s x) := by
    apply (integral_eq_iff_of_ae_le hip (his.const_mul d) hle2).mp
    rw [hp,integral_const_mul,hmass]
    ring
  exact he1.symm.trans he2

/-- Half-set images under two regular symmetric kernels with disjoint images.
The degree hypotheses are almost everywhere, not pointwise. -/
theorem half_set_transport
    (C D : Ω × Ω → ℝ) (hC : Measurable C) (hD : Measurable D)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (d : ℝ) (hd : 0 < d)
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ S=(1:ENNReal)/2)
    (hz : ∫ x, act μ C (oneSet S) x*act μ D (oneSet S) x ∂μ=0) :
    ∃ U : Set Ω, MeasurableSet U ∧ μ U=(1:ENNReal)/2 ∧
      act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet U x) ∧
      act μ D (oneSet S) =ᵐ[μ] (fun x => d*oneSet Uᶜ x) ∧
      act μ C (oneSet U) =ᵐ[μ] (fun x => d*oneSet S x) ∧
      act μ C (act μ C (oneSet S)) =ᵐ[μ] (fun x => d^2*oneSet S x) := by
  have hmS := oneSet_measurable S hS
  have bmS := oneSet_bounds S
  have hiS : (∫ x, oneSet S x ∂μ)=(1:ℝ)/2 := by
    calc
      _ = μ.real S := integral_indicator_one hS
      _ = _ := by simp [measureReal_def,mS]
  have hf := measurable_act μ C (oneSet S) hC hmS
  have hg := measurable_act μ D (oneSet S) hD hmS
  have bf := act_bounds μ C (oneSet S) hC hmS bC bmS
  have bg := act_bounds μ D (oneSet S) hD hmS bD bmS
  have bfd : ∀ᵐ x ∂μ, 0 ≤ act μ C (oneSet S) x ∧ act μ C (oneSet S) x ≤ d := by
    filter_upwards [rC] with x hx
    exact ⟨(bf x).1,(act_le_row μ C (oneSet S) hC hmS bC bmS x).trans_eq hx⟩
  have bgd : ∀ᵐ x ∂μ, 0 ≤ act μ D (oneSet S) x ∧ act μ D (oneSet S) x ≤ d := by
    filter_upwards [rD] with x hx
    exact ⟨(bg x).1,(act_le_row μ D (oneSet S) hD hmS bD bmS x).trans_eq hx⟩
  have hz' : ∀ᵐ x ∂μ, act μ C (oneSet S) x*act μ D (oneSet S) x=0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (bf x).1 (bg x).1))
      (unit_integrable μ _ (hf.mul hg) (fun x => mul_unit (bf x) (bg x)))).mp hz
  have htf : (∫ x, act μ C (oneSet S) x ∂μ)=d/2 := by
    rw [act_total μ C (oneSet S) hC hmS bC bmS sC d rC,hiS]; ring
  have htg : (∫ x, act μ D (oneSet S) x ∂μ)=d/2 := by
    rw [act_total μ D (oneSet S) hD hmS bD bmS sD d rD,hiS]; ring
  obtain ⟨U,hU,mU,heC,heD⟩ := TwoPairHalfTransport.disjoint_images_saturate_ae μ
    (act μ C (oneSet S)) (act μ D (oneSet S)) d hd hf hg bfd bgd hz' htf htg
  have hfe : act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet U x) := by
    filter_upwards [heC] with x hx
    by_cases hu : x ∈ U <;> simpa [oneSet,hu] using hx
  have hge : act μ D (oneSet S) =ᵐ[μ] (fun x => d*oneSet Uᶜ x) := by
    filter_upwards [heD] with x hx
    by_cases hu : x ∈ U <;> simpa [oneSet,hu] using hx
  have hmU := oneSet_measurable U hU
  have bmU := oneSet_bounds U
  have hiU : (∫ x, oneSet U x ∂μ)=(1:ℝ)/2 := by
    calc
      _ = μ.real U := integral_indicator_one hU
      _ = _ := by simp [measureReal_def,mU]
  have hrevtotal : (∫ x, act μ C (oneSet U) x ∂μ)=d/2 := by
    rw [act_total μ C (oneSet U) hC hmU bC bmU sC d rC,hiU]; ring
  have hrevpair : (∫ x, oneSet S x*act μ C (oneSet U) x ∂μ)=d/2 := by
    rw [act_pairing μ C (oneSet S) (oneSet U) hC hmS hmU bC bmS bmU sC]
    calc
      _ = ∫ x, d*oneSet U x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfe] with x hx
        rw [hx]
        rcases oneSet_binary U x with h | h <;> simp [h]
      _ = _ := by rw [integral_const_mul,hiU]; ring
  have hrev : act μ C (oneSet U) =ᵐ[μ] (fun x => d*oneSet S x) := by
    apply recover_capped_indicator μ _ _ (measurable_act μ C (oneSet U) hC hmU) hmS
      d hd _ (oneSet_binary S) hiS hrevtotal hrevpair
    filter_upwards [rC] with x hx
    exact ⟨(act_bounds μ C (oneSet U) hC hmU bC bmU x).1,
      (act_le_row μ C (oneSet U) hC hmU bC bmU x).trans_eq hx⟩
  refine ⟨U,hU,mU,hfe,hge,hrev,?_⟩
  filter_upwards [hrev] with x hx
  have he : act μ C (act μ C (oneSet S)) x=d*act μ C (oneSet U) x := by
    unfold act
    calc
      _ = ∫ y, C (x,y)*(d*oneSet U y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfe] with y hy
        change C (x,y)*act μ C (oneSet S) y=C (x,y)*(d*oneSet U y)
        rw [hy]
      _ = _ := by rw [← integral_const_mul]; congr 1; funext y; ring
  rw [he,hx]
  ring
end TwoPairHalfSetOperator
namespace TwoPairHalfSetOperator
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma act_comp_square (C : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hC : Measurable C) (hf : Measurable f)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : Ω) :
    act μ (comp μ C C) f x=act μ C (act μ C f) x := by
  have hi : Integrable (fun p : Ω × Ω => C (x,p.1)*(C p*f p.2)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bC _) (mul_unit (bC _) (bf _)))
  calc
    _ = ∫ y, ∫ z, C (x,z)*(C (z,y)*f y) ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∫ z, C (x,z)*C (z,y) ∂μ)*f y = _
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by dsimp only; ring)
    _ = ∫ z, ∫ y, C (x,z)*(C (z,y)*f y) ∂μ ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => integral_const_mul _ _)

theorem half_set_square_preservation
    (C D : Ω × Ω → ℝ) (hC : Measurable C) (hD : Measurable D)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (d : ℝ) (hd : 0 < d)
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ S=(1:ENNReal)/2)
    (hz : ∫ x, act μ C (oneSet S) x*act μ D (oneSet S) x ∂μ=0) :
    act μ (comp μ C C) (oneSet S) =ᵐ[μ] (fun x => d^2*oneSet S x) := by
  obtain ⟨U,hU,mU,hCim,hDim,hrev,hsq⟩ :=
    half_set_transport μ C D hC hD bC bD sC sD d hd rC rD S hS mS hz
  filter_upwards [hsq] with x hx
  rw [act_comp_square μ C (oneSet S) hC (oneSet_measurable S hS) bC (oneSet_bounds S) x]
  exact hx
end TwoPairHalfSetOperator
end


-- Local module: TwoPairSquareSupport
section
open MeasureTheory
namespace TwoPairSquareSupport
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A positive-degree symmetric kernel cannot erase support after two applications. -/
lemma square_preserves_support (F : Ω × Ω → ℝ) (g : Ω → ℝ)
    (hF : Measurable F) (hg : Measurable g)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (sF : ∀ x y, F (x,y)=F (y,x)) (d : ℝ) (hd : 0 < d)
    (rF : ∀ᵐ x ∂μ, ∫ y, F (x,y) ∂μ=d) :
    ∀ᵐ x ∂μ, 0 < g x → 0 < act μ F (act μ F g) x := by
  classical
  let S : Set Ω := {x | act μ F (act μ F g) x=0}
  have hS : MeasurableSet S := measurableSet_eq_fun
    (measurable_act μ F (act μ F g) hF (measurable_act μ F g hF hg)) measurable_const
  let f : Ω → ℝ := S.indicator g
  have hf : Measurable f := hg.indicator hS
  have bf (x : Ω) : 0 ≤ f x ∧ f x ≤ 1 := by
    by_cases hx : x ∈ S <;> simp [f,hx,bg x]
  have hfg (x : Ω) : f x ≤ g x := by
    by_cases hx : x ∈ S <;> simp [f,hx,(bg x).1]
  have hFg := measurable_act μ F g hF hg
  have hFf := measurable_act μ F f hF hf
  have bFg := act_bounds μ F g hF hg bF bg
  have bFf := act_bounds μ F f hF hf bF bf
  have horder (x : Ω) : act μ F f x ≤ act μ F g x := by
    apply integral_mono
      (unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bF _) (bf _)))
      (unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bF _) (bg _)))
    intro y
    exact mul_le_mul_of_nonneg_left (hfg y) (bF (x,y)).1
  have hpair : (∫ x, act μ F g x*act μ F f x ∂μ)=0 := by
    rw [← act_pairing μ F f (act μ F g) hF hf hFg bF bf bFg sF]
    have he : (fun x => f x*act μ F (act μ F g) x) = fun _ => (0:ℝ) := by
      funext x
      by_cases hx : x ∈ S
      · have hz : act μ F (act μ F g) x=0 := hx
        simp [hz]
      · simp [f,hx]
    rw [he,integral_zero]
  have hpzero : ∀ᵐ x ∂μ, act μ F g x*act μ F f x=0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (bFg x).1 (bFf x).1)
      (unit_integrable μ _ (hFg.mul hFf) (fun x => mul_unit (bFg x) (bFf x)))).mp hpair
  have hFzero : act μ F f =ᵐ[μ] fun _ => 0 := by
    filter_upwards [hpzero] with x hx
    have ho := horder x
    have hn := (bFf x).1
    nlinarith
  have hmass : (∫ x, f x ∂μ)=0 := by
    have hi := act_total μ F f hF hf bF bf sF d rF
    have hz : (∫ x, act μ F f x ∂μ)=0 := by
      rw [integral_congr_ae hFzero,integral_zero]
    rw [hz] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left (ne_of_gt hd)
  have hfzero : f =ᵐ[μ] fun _ => 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => (bf x).1)
      (unit_integrable μ f hf bf)).mp hmass
  filter_upwards [hfzero] with x hx
  intro hp
  have hn := (act_bounds μ F (act μ F g) hF hFg bF bFg x).1
  apply lt_of_le_of_ne hn
  intro hz
  have hs : x ∈ S := hz.symm
  have hgz : g x=0 := by simpa [f,hs] using hx
  exact (ne_of_gt hp) hgz

/-- Kernel version: the support inclusion holds on the product measure. -/
lemma kernel_square_preserves_support (F G : Ω × Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (sF : ∀ x y, F (x,y)=F (y,x)) (d : ℝ) (hd : 0 < d)
    (rF : ∀ᵐ x ∂μ, ∫ y, F (x,y) ∂μ=d) :
    ∀ᵐ p ∂μ.prod μ, 0 < G p → 0 < comp μ F (comp μ F G) p := by
  have hm : MeasurableSet {p : Ω × Ω | 0 < G p → 0 < comp μ F (comp μ F G) p} :=
    (measurableSet_lt measurable_const hG).imp
      (measurableSet_lt measurable_const (measurable_comp μ F (comp μ F G) hF
        (measurable_comp μ F G hF hG)))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  apply (Measure.ae_ae_comm hm).mpr
  apply Filter.Eventually.of_forall
  intro y
  simpa only [act,comp] using square_preserves_support μ F (fun z => G (z,y))
    hF (by fun_prop) bF (fun z => bG (z,y)) sF d hd rF

/-- A zero nonnegative pairing with the longer path also vanishes for the shorter path. -/
lemma remove_square_from_zero_pairing (F G T : Ω × Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hT : Measurable T)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (bT : ∀ p, 0 ≤ T p ∧ T p ≤ 1)
    (sF : ∀ x y, F (x,y)=F (y,x)) (d : ℝ) (hd : 0 < d)
    (rF : ∀ᵐ x ∂μ, ∫ y, F (x,y) ∂μ=d)
    (hz : (∫ p, T p * comp μ F (comp μ F G) p ∂μ.prod μ)=0) :
    (∫ p, T p*G p ∂μ.prod μ)=0 := by
  have hFG := measurable_comp μ F G hF hG
  have bFG := comp_bounds μ F G hF hG bF bG
  have hFFG := measurable_comp μ F (comp μ F G) hF hFG
  have bFFG := comp_bounds μ F (comp μ F G) hF hFG bF bFG
  have he : ∀ᵐ p ∂μ.prod μ, T p*comp μ F (comp μ F G) p=0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun p => mul_nonneg (bT p).1 (bFFG p).1)
      (unit_integrable _ _ (hT.mul hFFG) (fun p => mul_unit (bT p) (bFFG p)))).mp hz
  have hs := kernel_square_preserves_support μ F G hF hG bF bG sF d hd rF
  have hzero : (fun p => T p*G p) =ᵐ[μ.prod μ] fun _ => 0 := by
    filter_upwards [he,hs] with p hp hsp
    rcases eq_or_lt_of_le (bG p).1 with hg | hg
    · rw [← hg,mul_zero]
    · have ht : T p=0 := (mul_eq_zero.mp hp).resolve_right (ne_of_gt (hsp hg))
      rw [ht,zero_mul]
  rw [integral_congr_ae hzero,integral_zero]

end TwoPairSquareSupport

end


-- Local module: TwoPairCycleReduction
section
open MeasureTheory
namespace TwoPairCycleReduction
open FourColorKernels
open Submissions.E811LowSupport.Paths
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def closing4 (A B C D : Ω × Ω → ℝ) : ℝ :=
  ∫ p, D (p.2,p.1)*comp μ A (comp μ B C) p ∂μ.prod μ

/-- Remove an adjacent repeated color from a vanishing six-cycle. -/
lemma remove_repeated_prefix (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (he : W 1 = W 0) (hs : ∀ x y, W 0 (x,y)=W 0 (y,x))
    (d : ℝ) (hd : 0 < d)
    (hr : ∀ᵐ x ∂μ, ∫ y, W 0 (x,y) ∂μ=d)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    closing4 μ (W 2) (W 3) (W 4) (W 5)=0 := by
  have hc : LowSupportCyclePath.closing (μ := μ) W=0 := by
    rw [LowSupportCyclePath.closing_eq_cycle_pointwise W hm hb,hz]
  have hm34 := measurable_comp μ (W 3) (W 4) (hm 3) (hm 4)
  have hb34 := comp_bounds μ (W 3) (W 4) (hm 3) (hm 4) (hb 3) (hb 4)
  have hm234 := measurable_comp μ (W 2) (comp μ (W 3) (W 4)) (hm 2) hm34
  have hb234 := comp_bounds μ (W 2) (comp μ (W 3) (W 4)) (hm 2) hm34 (hb 2) hb34
  apply TwoPairSquareSupport.remove_square_from_zero_pairing μ (W 0)
    (comp μ (W 2) (comp μ (W 3) (W 4))) (fun p => W 5 (p.2,p.1))
    (hm 0) hm234 ((hm 5).comp measurable_swap) (hb 0) hb234
    (fun p => hb 5 (p.2,p.1)) hs d hd hr
  simpa only [LowSupportCyclePath.closing,pathKernel,comp,he,mul_comm] using hc

end TwoPairCycleReduction
end


-- Local module: TwoPairFourCycleProducts
section
open MeasureTheory
namespace TwoPairFourCycleProducts
open FourColorKernels TwoPairCycleReduction TwoPairCompositionAlgebra TwoPairTraceAlgebra
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma closing4_pairing (A B C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1) :
    closing4 μ A B C D = ∫ p, comp μ A B p*comp μ C D (p.2,p.1) ∂μ.prod μ := by
  have he : closing4 μ A B C D =
      ∫ p, comp μ (comp μ A B) C p*D (p.2,p.1) ∂μ.prod μ := by
    unfold closing4
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    dsimp only
    rw [comp_assoc μ A B C hA hB hC bA bB bC]
    ring
  rw [he]
  exact pairing_comp_left μ (comp μ A B) C D
    (measurable_comp μ A B hA hB) hC hD (comp_bounds μ A B hA hB bA bB) bC bD

lemma repeated_product_zero (A C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (hz : closing4 μ A A C D=0) :
    ∀ᵐ p ∂μ.prod μ, comp μ A A p*(comp μ C D p+comp μ D C p)=0 := by
  have hAA := measurable_comp μ A A hA hA
  have bAA := comp_bounds μ A A hA hA bA bA
  have hDC := measurable_comp μ D C hD hC
  have bDC := comp_bounds μ D C hD hC bD bC
  have hi : (∫ p, comp μ A A p*comp μ D C p ∂μ.prod μ)=0 := by
    rw [closing4_pairing μ A A C D hA hA hC hD bA bA bC bD] at hz
    have he : (fun p => comp μ A A p*comp μ C D (p.2,p.1)) =
        fun p => comp μ A A p*comp μ D C p := by
      funext p
      rw [comp_swap μ C D sC sD p.2 p.1]
    rwa [he] at hz
  have h0 : ∀ᵐ p ∂μ.prod μ, comp μ A A p*comp μ D C p=0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => mul_nonneg (bAA p).1 (bDC p).1)
      (unit_integrable _ _ (hAA.mul hDC) (fun p => mul_unit (bAA p) (bDC p)))).mp hi
  have h1 : ∀ᵐ p ∂μ.prod μ, comp μ A A (p.2,p.1)*comp μ D C (p.2,p.1)=0 :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae h0
  filter_upwards [h0,h1] with p hp hq
  rw [comp_swap μ A A sA sA p.2 p.1,comp_swap μ D C sD sC p.2 p.1] at hq
  rw [mul_add,hp,hq,zero_add]

end TwoPairFourCycleProducts
end


-- Local module: TwoPairKernelIdentities
section
open MeasureTheory
namespace TwoPairKernelIdentities
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma affine_product_integral (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun z => f z * g z) μ)
    (hrf : (∫ z, f z ∂μ) = (1 / 3 : ℝ))
    (hrg : (∫ z, g z ∂μ) = (1 / 3 : ℝ)) :
    (∫ z, ((1 - f z) / 2) * ((1 - g z) / 2) ∂μ) =
      (1 / 12 : ℝ) + (∫ z, f z * g z ∂μ) / 4 := by
  have he : (fun z => ((1 - f z) / 2) * ((1 - g z) / 2)) =
      fun z => ((1 - f z - g z) + f z * g z) / 4 := by
    funext z
    ring
  have h1 : Integrable (fun z => 1 - f z) μ := (integrable_const (1 : ℝ)).sub hf
  have h2 : Integrable (fun z => 1 - f z - g z) μ := h1.sub hg
  rw [he, integral_div, integral_add h2 hfg,
    integral_sub h1 hg, integral_sub (integrable_const (1 : ℝ)) hf, hrf, hrg]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

lemma complement_square_row (R : Ω × Ω → ℝ)
    (hm : Measurable R) (hb : ∀ p, 0 ≤ R p ∧ R p ≤ 1)
    (hs : ∀ x y, R (x,y) = R (y,x))
    (x y : Ω)
    (hx : (∫ z, R (x,z) ∂μ) = (1/3 : ℝ))
    (hy : (∫ z, R (y,z) ∂μ) = (1/3 : ℝ)) :
    comp μ (fun p => (1-R p)/2) (fun p => (1-R p)/2) (x,y) =
      (1/12 : ℝ) + comp μ R R (x,y)/4 := by
  have hix : Integrable (fun z => R (x,z)) μ :=
    unit_integrable μ _ (by fun_prop) (fun z => hb (x,z))
  have hiy : Integrable (fun z => R (z,y)) μ :=
    unit_integrable μ _ (by fun_prop) (fun z => hb (z,y))
  have hip : Integrable (fun z => R (x,z)*R (z,y)) μ :=
    unit_integrable μ _ (by fun_prop) (fun z => mul_unit (hb (x,z)) (hb (z,y)))
  have hry : (∫ z, R (z,y) ∂μ) = (1/3 : ℝ) := by
    simpa only [hs _ y] using hy
  exact affine_product_integral μ _ _ hix hiy hip hx hry

lemma complement_square_ae (R : Ω × Ω → ℝ)
    (hm : Measurable R) (hb : ∀ p, 0 ≤ R p ∧ R p ≤ 1)
    (hs : ∀ x y, R (x,y) = R (y,x))
    (hr : ∀ᵐ x ∂μ, (∫ z, R (x,z) ∂μ) = (1/3 : ℝ)) :
    ∀ᵐ p ∂μ.prod μ,
      comp μ (fun p => (1-R p)/2) (fun p => (1-R p)/2) p =
        (1/12 : ℝ) + comp μ R R p/4 := by
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [hr] with x hx
    filter_upwards [hr] with y hy
    exact complement_square_row μ R hm hb hs x y hx hy
  · exact measurableSet_eq_fun (measurable_comp μ _ _ (by fun_prop) (by fun_prop))
      (measurable_const.add ((measurable_comp μ R R hm hm).div_const 4))

end TwoPairKernelIdentities
end


-- Local module: TwoPairHalfSupportBridge
section
open MeasureTheory
namespace TwoPairHalfSupportBridge
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma remainder_square_dom
    (C D R : Ω × Ω → ℝ) (hC : Measurable C) (hD : Measurable D) (hR : Measurable R)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (bR : ∀ p, 0 ≤ R p ∧ R p ≤ 1) (he : ∀ p, R p=C p+D p) (p : Ω × Ω) :
    comp μ C D p+comp μ D C p ≤ comp μ R R p := by
  have hiCD : Integrable (fun z => C (p.1,z)*D (z,p.2)) μ :=
    unit_integrable μ _ (by fun_prop) (fun z => mul_unit (bC _) (bD _))
  have hiDC : Integrable (fun z => D (p.1,z)*C (z,p.2)) μ :=
    unit_integrable μ _ (by fun_prop) (fun z => mul_unit (bD _) (bC _))
  have hiRR : Integrable (fun z => R (p.1,z)*R (z,p.2)) μ :=
    unit_integrable μ _ (by fun_prop) (fun z => mul_unit (bR _) (bR _))
  unfold comp
  rw [← integral_add hiCD hiDC]
  apply integral_mono (hiCD.add hiDC) hiRR
  intro z
  change C (p.1,z)*D (z,p.2)+D (p.1,z)*C (z,p.2) ≤ R (p.1,z)*R (z,p.2)
  rw [he (p.1,z),he (z,p.2)]
  nlinarith [mul_nonneg (bC (p.1,z)).1 (bC (z,p.2)).1,
    mul_nonneg (bD (p.1,z)).1 (bD (z,p.2)).1]

lemma strict_overlap_of_identity
    (Q R L : Ω × Ω → ℝ) (sQ : ∀ x y, Q (x,y)=Q (y,x))
    (he : ∀ᵐ p ∂μ.prod μ, comp μ Q Q p=(1:ℝ)/12+comp μ R R p/4)
    (hd : ∀ᵐ p ∂μ.prod μ, L p ≤ comp μ R R p) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      (1:ℝ)/12 < ∫ z, Q (x,z)*Q (y,z) ∂μ := by
  have hh : ∀ᵐ p ∂μ.prod μ, 0 < L p →
      (1:ℝ)/12 < ∫ z, Q (p.1,z)*Q (p.2,z) ∂μ := by
    filter_upwards [he,hd] with p hp hd
    intro hL
    have hc : (1:ℝ)/12 < comp μ Q Q p := by linarith
    simpa only [comp,sQ p.2] using hc
  exact Measure.ae_ae_of_ae_prod hh

lemma square_zero_middle
    (P : Ω × Ω → ℝ) (hP : Measurable P)
    (bP : ∀ p, 0 ≤ P p ∧ P p ≤ 1) (sP : ∀ x y, P (x,y)=P (y,x))
    (x y : Ω) (hz : comp μ P P (x,y)=0) :
    ∀ᵐ u ∂μ, P (x,u)*P (y,u)=0 := by
  have hi : Integrable (fun u => P (x,u)*P (u,y)) μ :=
    unit_integrable μ _ (by fun_prop) (fun u => mul_unit (bP _) (bP _))
  have hh := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun u => mul_nonneg (bP (x,u)).1 (bP (u,y)).1)) hi).mp hz
  filter_upwards [hh] with u hu
  change P (x,u)*P (u,y)=0 at hu
  simpa only [sP y] using hu

/-- Both required Fubini interfaces follow from the single zero product P²·L. -/
lemma independence_and_disjointness
    (P L : Ω × Ω → ℝ) (hP : Measurable P) (hL : Measurable L)
    (bP : ∀ p, 0 ≤ P p ∧ P p ≤ 1) (sP : ∀ x y, P (x,y)=P (y,x))
    (hz : ∀ᵐ p ∂μ.prod μ, comp μ P P p*L p=0) :
    (∀ᵐ x ∂μ, ∀ᵐ p ∂μ.prod μ,
      0 < P (x,p.1) → 0 < P (x,p.2) → L p=0) ∧
    (∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ u ∂μ, ¬ (0 < P (x,u) ∧ 0 < P (y,u))) := by
  have ht : ∀ᵐ p ∂μ.prod μ, ∀ᵐ u ∂μ,
      L p*(P (p.1,u)*P (p.2,u))=0 := by
    filter_upwards [hz] with p hp
    rcases mul_eq_zero.mp hp with hc | hl
    · filter_upwards [square_zero_middle μ P hP bP sP p.1 p.2 hc] with u hu
      simp [hu]
    · exact Filter.Eventually.of_forall (fun u => by simp [hl])
  have ht' : ∀ᵐ u ∂μ, ∀ᵐ p ∂μ.prod μ,
      L p*(P (p.1,u)*P (p.2,u))=0 := by
    apply (Measure.ae_ae_comm (p := fun p u => L p*(P (p.1,u)*P (p.2,u))=0) ?_).mp ht
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  constructor
  · filter_upwards [ht'] with x hx
    filter_upwards [hx] with p hp
    intro h1 h2
    have hn : P (p.1,x)*P (p.2,x) ≠ 0 := by
      apply ne_of_gt
      simpa only [sP x] using mul_pos h1 h2
    exact (mul_eq_zero.mp hp).resolve_right hn
  · have htt := Measure.ae_ae_of_ae_prod ht
    filter_upwards [htt] with x hx
    filter_upwards [hx] with y hy
    intro hxy
    filter_upwards [hy] with u hu
    intro hp
    have hn : 0 < L (x,y)*(P (x,u)*P (y,u)) := mul_pos hxy (mul_pos hp.1 hp.2)
    linarith
end TwoPairHalfSupportBridge
namespace TwoPairHalfSupportBridge
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma same_rows_from_products
    (A B L : Ω × Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (hzA : ∀ᵐ p ∂μ.prod μ, comp μ A A p*L p=0)
    (hzB : ∀ᵐ p ∂μ.prod μ, comp μ B B p*L p=0) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      ∀ᵐ z ∂μ, A (x,z)*A (y,z)=0 ∧ B (x,z)*B (y,z)=0 := by
  have hh : ∀ᵐ p ∂μ.prod μ, 0 < L p →
      ∀ᵐ z ∂μ, A (p.1,z)*A (p.2,z)=0 ∧ B (p.1,z)*B (p.2,z)=0 := by
    filter_upwards [hzA,hzB] with p ha hb
    intro hp
    have ha0 := (mul_eq_zero.mp ha).resolve_right (ne_of_gt hp)
    have hb0 := (mul_eq_zero.mp hb).resolve_right (ne_of_gt hp)
    exact (square_zero_middle μ A hA bA sA p.1 p.2 ha0).and
      (square_zero_middle μ B hB bB sB p.1 p.2 hb0)
  exact Measure.ae_ae_of_ae_prod hh

lemma mixed_zero_middle
    (A B : Ω × Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (sB : ∀ x y, B (x,y)=B (y,x)) (x y : Ω)
    (hz : comp μ A B (x,y)=0) : ∀ᵐ z ∂μ, A (x,z)*B (y,z)=0 := by
  have hi : Integrable (fun z => A (x,z)*B (z,y)) μ :=
    unit_integrable μ _ (by fun_prop) (fun z => mul_unit (bA _) (bB _))
  have hh := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z => mul_nonneg (bA (x,z)).1 (bB (z,y)).1)) hi).mp hz
  filter_upwards [hh] with z hz
  change A (x,z)*B (z,y)=0 at hz
  simpa only [sB y] using hz

lemma missing_rows_from_identity
    (A B P : Ω × Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (he : ∀ᵐ p ∂μ.prod μ, P p=comp μ A B p+comp μ B A p) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, P (x,y)=0 →
      ∀ᵐ z ∂μ, A (x,z)*B (y,z)=0 ∧ B (x,z)*A (y,z)=0 := by
  have hh : ∀ᵐ p ∂μ.prod μ, P p=0 →
      ∀ᵐ z ∂μ, A (p.1,z)*B (p.2,z)=0 ∧ B (p.1,z)*A (p.2,z)=0 := by
    filter_upwards [he] with p hp
    intro hz
    have hAB := (comp_bounds μ A B hA hB bA bB p).1
    have hBA := (comp_bounds μ B A hB hA bB bA p).1
    have hAB0 : comp μ A B p=0 := by linarith
    have hBA0 : comp μ B A p=0 := by linarith
    exact (mixed_zero_middle μ A B hA hB bA bB sB p.1 p.2 hAB0).and
      (mixed_zero_middle μ B A hB hA bB bA sA p.1 p.2 hBA0)
  exact Measure.ae_ae_of_ae_prod hh
end TwoPairHalfSupportBridge
namespace TwoPairHalfSupportBridge
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Saturation directly from measurable composition identities and zero products. -/
theorem half_support_from_compositions
    (A B P L R : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hP : Measurable P) (hL : Measurable L)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bP : ∀ p, 0 ≤ P p ∧ P p ≤ 1) (bL : ∀ p, 0 ≤ L p ∧ L p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (sP : ∀ x y, P (x,y)=P (y,x)) (sL : ∀ x y, L (x,y)=L (y,x))
    (bQ : ∀ x z, 0 ≤ A (x,z)+B (x,z) ∧ A (x,z)+B (x,z) ≤ 1/2)
    (rQ : ∀ᵐ u ∂μ, ∫ z, (A (u,z)+B (u,z)) ∂μ = (1:ℝ)/3)
    (d : ℝ) (hd : 0 < d) (rL : ∀ᵐ x ∂μ, ∫ y, L (x,y) ∂μ=d)
    (eP : ∀ᵐ p ∂μ.prod μ, P p=comp μ A B p+comp μ B A p)
    (eQ : ∀ᵐ p ∂μ.prod μ,
      comp μ (fun p => A p+B p) (fun p => A p+B p) p=(1:ℝ)/12+comp μ R R p/4)
    (hdom : ∀ᵐ p ∂μ.prod μ, L p ≤ comp μ R R p)
    (hzA : ∀ᵐ p ∂μ.prod μ, comp μ A A p*L p=0)
    (hzB : ∀ᵐ p ∂μ.prod μ, comp μ B B p*L p=0)
    (hzP : ∀ᵐ p ∂μ.prod μ, comp μ P P p*L p=0) :
    ∀ᵐ x ∂μ, μ {y | 0 < P (x,y)} = (1:ENNReal)/2 := by
  obtain ⟨hind,hdis⟩ := independence_and_disjointness μ P L hP hL bP sP hzP
  apply TwoPairHalfSupport.half_support μ A B P L hA hB hP hL
    (fun p => (bP p).1) bL sL bQ rQ d hd rL
  · exact missing_rows_from_identity μ A B P hA hB bA bB sA sB eP
  · exact same_rows_from_products μ A B L hA hB bA bB sA sB hzA hzB
  · exact strict_overlap_of_identity μ (fun p => A p+B p) R L
      (fun x y => by rw [sA x y,sB x y]) eQ hdom
  · exact hind
  · exact hdis
end TwoPairHalfSupportBridge
end


-- Local module: TwoPairRowConfinement
section
open MeasureTheory
namespace TwoPairRowConfinement
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A binary eigenfunction with eigenvalue equal to the row degree cannot change
across a positive kernel edge. Symmetry of the kernel is not needed for this step. -/
lemma invariant_cut_no_crossing
    (K : Ω × Ω → ℝ) (hK : Measurable K) (bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1)
    (k : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ=k)
    (s : Ω → ℝ) (hs : Measurable s) (bs : ∀ x, s x=0 ∨ s x=1)
    (he : ∀ᵐ x ∂μ, act μ K s x=k*s x) :
    ∀ᵐ p ∂μ.prod μ, 0 < K p → s p.1=s p.2 := by
  have hmeas : MeasurableSet {p : Ω × Ω | 0 < K p → s p.1=s p.2} :=
    (measurableSet_lt measurable_const hK).imp
      (measurableSet_eq_fun (hs.comp measurable_fst) (hs.comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [hr,he] with x hx hex
  have bs' (y : Ω) : 0 ≤ s y ∧ s y ≤ 1 := by rcases bs y with h | h <;> simp [h]
  have hiK : Integrable (fun y => K (x,y)) μ :=
    unit_integrable μ _ (by fun_prop) (fun y => bK (x,y))
  have hiKs : Integrable (fun y => K (x,y)*s y) μ :=
    unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bK _) (bs' _))
  rcases bs x with hsx | hsx
  · have hz : (∫ y, K (x,y)*s y ∂μ)=0 := by
      change (∫ y, K (x,y)*s y ∂μ)=k*s x at hex
      simpa [hsx] using hex
    have hzero := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => mul_nonneg (bK (x,y)).1 (bs' y).1)) hiKs).mp hz
    filter_upwards [hzero] with y hy
    intro hxy
    change K (x,y)*s y=0 at hy
    have hsy := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hxy)
    exact hsx.trans hsy.symm
  · have hic : Integrable (fun y => K (x,y)*(1-s y)) μ :=
      unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bK _)
        ⟨by linarith [(bs' y).2],by linarith [(bs' y).1]⟩)
    have hz : (∫ y, K (x,y)*(1-s y) ∂μ)=0 := by
      calc
        _ = ∫ y, K (x,y)-K (x,y)*s y ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y => by dsimp only; ring)
        _ = 0 := by
          rw [integral_sub hiK hiKs,hx]
          change (∫ y, K (x,y)*s y ∂μ)=k*s x at hex
          rw [hex,hsx]
          ring
    have hzero := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => mul_nonneg (bK (x,y)).1
        (by linarith [(bs' y).2]))) hic).mp hz
    filter_upwards [hzero] with y hy
    intro hxy
    change K (x,y)*(1-s y)=0 at hy
    have hsy := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hxy)
    rw [hsx]
    linarith

/-- If every binary H-row is preserved by K, positive K edges join AE-equal H rows. -/
theorem row_confinement
    (K H : Ω × Ω → ℝ) (hK : Measurable K) (hH : Measurable H)
    (bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1)
    (bH : ∀ p, H p=0 ∨ H p=1)
    (sH : ∀ x y, H (x,y)=H (y,x))
    (k : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ=k)
    (he : ∀ᵐ z ∂μ, ∀ᵐ x ∂μ, act μ K (fun y => H (z,y)) x=k*H (z,x)) :
    ∀ᵐ p ∂μ.prod μ, 0 < K p →
      (fun z => H (p.1,z)) =ᵐ[μ] (fun z => H (p.2,z)) := by
  have ht : ∀ᵐ z ∂μ, ∀ᵐ p ∂μ.prod μ, 0 < K p → H (z,p.1)=H (z,p.2) := by
    filter_upwards [he] with z hz
    exact invariant_cut_no_crossing μ K hK bK k hr
      (fun y => H (z,y)) (hH.comp (measurable_const.prodMk measurable_id))
      (fun y => bH (z,y)) hz
  have ht' : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂μ, 0 < K p → H (z,p.1)=H (z,p.2) := by
    apply (Measure.ae_ae_comm (p := fun z p => 0 < K p → H (z,p.1)=H (z,p.2)) ?_).mp ht
    exact (measurableSet_lt measurable_const (hK.comp measurable_snd)).imp
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))
  filter_upwards [ht'] with p hp
  intro hkp
  filter_upwards [hp] with z hz
  simpa only [sH p.1,sH p.2] using hz hkp
end TwoPairRowConfinement
end


-- Local module: FourColorClasses
section
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
end


-- Local module: FourColorRowDistance
section
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
end


-- Local module: TwoPairFiniteClasses
section

open MeasureTheory
open scoped BigOperators

namespace TwoPairFiniteClasses
variable {Ω : Type*} [MeasurableSpace Ω]

theorem finite_six_of_disjoint_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Set (Set Ω)) (hm : ∀ S ∈ F, MeasurableSet S)
    (hp : ∀ S ∈ F, (1 / 6 : ℝ) ≤ μ.real S)
    (hd : F.PairwiseDisjoint id) : F.Finite ∧ F.ncard ≤ 6 := by
  classical
  have hp' : ∀ S ∈ F, (1 : ENNReal) / 6 ≤ μ S := by
    intro S hS
    apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top μ S)).mp
    simpa [measureReal_def] using hp S hS
  have hf := Measure.finite_const_le_meas_of_disjoint_iUnion μ
    (show (0 : ENNReal) < 1 / 6 by norm_num)
    (fun i : F => hm i.val i.property)
    (fun i j hij => hd i.property j.property (fun he => hij (Subtype.ext he)))
    (measure_ne_top μ _)
  have he : {i : F | (1 : ENNReal) / 6 ≤ μ i.val} = Set.univ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hp' i.val i.property
  rw [he] at hf
  have hfin : F.Finite := Set.finite_coe_iff.mp (Set.finite_univ_iff.mp hf)
  let t := hfin.toFinset
  have hsum : (∑ S ∈ t, μ.real S) ≤ 1 := by
    have h := sum_measureReal_le_measureReal_univ (μ := μ) (s := t) (t := id)
      (fun S hS => hm S (by simpa [t] using hS))
      (by simpa [t] using hd)
    simpa using h
  have hlo : (t.card : ℝ) * (1 / 6) ≤ ∑ S ∈ t, μ.real S := by
    calc
      _ = ∑ _S ∈ t, (1 / 6 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun S hS => hp S (by simpa [t] using hS))
  have hc : t.card ≤ 6 := by
    have hr : (t.card : ℝ) ≤ 6 := by linarith
    exact_mod_cast hr
  exact ⟨hfin, by simpa [Set.ncard_eq_toFinset_card F hfin, t] using hc⟩

/-- A row of mass 1/36 bounded by 1/6 and confined to X forces mass(X)≥1/6. -/
theorem mass_of_supported_row (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Set Ω) (hX : MeasurableSet X) (f : Ω → ℝ)
    (hi : Integrable f μ) (hb : ∀ᵐ y ∂μ, f y ≤ (1 / 6 : ℝ))
    (hs : ∀ᵐ y ∂μ, y ∉ X → f y = 0)
    (hr : ∫ y, f y ∂μ = (1 / 36 : ℝ)) : (1 / 6 : ℝ) ≤ μ.real X := by
  classical
  have hle : f ≤ᵐ[μ] X.indicator (fun _ => (1 / 6 : ℝ)) := by
    filter_upwards [hb, hs] with y hy hz
    by_cases h : y ∈ X
    · simpa [Set.indicator_of_mem h] using hy
    · simp [Set.indicator_of_notMem h, hz h]
  have ht := integral_mono_ae hi ((integrable_const (1 / 6 : ℝ)).indicator hX) hle
  rw [hr, integral_indicator_const _ hX] at ht
  simp only [smul_eq_mul] at ht
  linarith

/-- The finite-class wrapper takes the support/moment facts supplied by C². -/
theorem finite_twin_classes (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H K : Ω × Ω → ℝ) (hm : Measurable H)
    (hb : ∀ p, 0 ≤ H p ∧ H p ≤ 1)
    (G : Set Ω) (hG : MeasurableSet G)
    (hi : ∀ x ∈ G, Integrable (fun y => K (x,y)) μ)
    (hcap : ∀ x ∈ G, ∀ᵐ y ∂μ, K (x,y) ≤ (1 / 6 : ℝ))
    (hs : ∀ x ∈ G, ∀ᵐ y ∂μ,
      ¬ (y ∈ G ∧ (fun z => H (x,z)) =ᵐ[μ] (fun z => H (y,z))) → K (x,y) = 0)
    (hr : ∀ x ∈ G, ∫ y, K (x,y) ∂μ = (1 / 36 : ℝ)) :
    let R := fun x y => (fun z => H (x,z)) =ᵐ[μ] (fun z => H (y,z))
    (FourColorClasses.classFamily G R).Finite ∧
      (FourColorClasses.classFamily G R).ncard ≤ 6 := by
  dsimp only
  let R := fun x y => (fun z => H (x,z)) =ᵐ[μ] (fun z => H (y,z))
  have hmC : ∀ x ∈ G, MeasurableSet (FourColorClasses.classSet G R x) := by
    intro x hx
    exact hG.inter (FourColorRowDistance.measurable_twin_class μ H hm hb x)
  have hpC : ∀ x ∈ G, (1 / 6 : ℝ) ≤ μ.real (FourColorClasses.classSet G R x) := by
    intro x hx
    exact mass_of_supported_row μ _ (hmC x hx) _ (hi x hx) (hcap x hx) (hs x hx) (hr x hx)
  have he := FourColorRowDistance.twin_equivalence μ H
  have hpart := FourColorClasses.positive_equivalence_partition μ G R
    (fun x _ => he.refl x) (fun x _ y _ h => he.symm h)
    (fun x _ y _ z _ h h' => he.trans h h') hmC
    (fun x hx => by
      have hh : 0 < μ.real (FourColorClasses.classSet G R x) := by linarith [hpC x hx]
      exact ENNReal.toReal_pos_iff.mp hh |>.1)
  apply finite_six_of_disjoint_mass μ _ (fun S hS => (hpart.2.1 S hS).1) _ hpart.2.2.1
  rintro S ⟨x,hx,rfl⟩
  exact hpC x hx

end TwoPairFiniteClasses
end


-- Local module: FourColorEqualRows
section
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
end


-- Local module: FourColorTwinExtraction
section
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
end


-- Local module: TwoPairClassExtraction
section

open MeasureTheory
namespace TwoPairClassExtraction
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cap on a square-composition row follows from the first factor's row integral. -/
theorem square_cap (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Ω × Ω → ℝ) (hm : Measurable C)
    (hb : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (x : Ω)
    (hr : ∫ y, C (x,y) ∂μ = (1 / 6 : ℝ)) (y : Ω) :
    FourColorKernels.comp μ C C (x,y) ≤ (1 / 6 : ℝ) := by
  have hi := FourColorKernels.unit_integrable μ (fun z => C (x,z)*C (z,y))
    (by fun_prop) (fun z => FourColorKernels.mul_unit (hb (x,z)) (hb (z,y)))
  have hj := FourColorKernels.unit_integrable μ (fun z => C (x,z))
    (by fun_prop) (fun z => hb (x,z))
  have h := integral_mono hi hj (fun z => mul_le_of_le_one_right (hb (x,z)).1 (hb (z,y)).2)
  simpa [FourColorKernels.comp, hr] using h

/-- Extract the finite measurable H-twin partition from actual C² confinement. -/
theorem extract_classes (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C H : Ω × Ω → ℝ) (hC : Measurable C) (hH : Measurable H)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bH : ∀ p, H p = 0 ∨ H p = 1)
    (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ = (1 / 6 : ℝ))
    (hconf : ∀ᵐ p ∂μ.prod μ, 0 < FourColorKernels.comp μ C C p →
      (fun z => H (p.1,z)) =ᵐ[μ] (fun z => H (p.2,z))) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ x ∂μ, x ∈ G) ∧
      let R := fun x y => (fun z => H (x,z)) =ᵐ[μ] (fun z => H (y,z))
      (∀ x ∈ G, MeasurableSet (FourColorClasses.classSet G R x) ∧
        (1 / 6 : ℝ) ≤ μ.real (FourColorClasses.classSet G R x)) ∧
      (FourColorClasses.classFamily G R).Finite ∧
      (FourColorClasses.classFamily G R).ncard ≤ 6 ∧
      (FourColorClasses.classFamily G R).PairwiseDisjoint id ∧
      ⋃₀ FourColorClasses.classFamily G R = G := by
  let K := FourColorKernels.comp μ C C
  let R := fun x y => (fun z => H (x,z)) =ᵐ[μ] (fun z => H (y,z))
  have hK : Measurable K := FourColorKernels.measurable_comp μ C C hC hC
  have bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1 :=
    FourColorKernels.comp_bounds μ C C hC hC bC bC
  have bH' : ∀ p, 0 ≤ H p ∧ H p ≤ 1 := by
    intro p
    rcases bH p with h | h <;> simp [h]
  have hkr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ = (1 / 36 : ℝ) := by
    simpa only [show (1 / 6 : ℝ) * (1 / 6) = 1 / 36 by norm_num] using
      FourColorKernels.comp_row μ C C hC hC bC bC (1/6) (1/6) hr hr
  have hcr : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < K (x,y) → R x y :=
    Measure.ae_ae_of_ae_prod hconf
  obtain ⟨G,hG,hGa,hgood⟩ := FourColorTwinExtraction.measurable_good_subset μ
    (fun x => (∫ y, C (x,y) ∂μ = (1 / 6 : ℝ)) ∧
      (∫ y, K (x,y) ∂μ = (1 / 36 : ℝ)) ∧
      (∀ᵐ y ∂μ, 0 < K (x,y) → R x y)) (hr.and (hkr.and hcr))
  have hi (x : Ω) : Integrable (fun y => K (x,y)) μ :=
    FourColorKernels.unit_integrable μ _ (by fun_prop) (fun y => bK (x,y))
  have hcap (x : Ω) (hx : x ∈ G) : ∀ᵐ y ∂μ, K (x,y) ≤ (1 / 6 : ℝ) :=
    Filter.Eventually.of_forall (square_cap μ C hC bC x (hgood x hx).1)
  have hs (x : Ω) (hx : x ∈ G) : ∀ᵐ y ∂μ,
      ¬ (y ∈ G ∧ R x y) → K (x,y) = 0 := by
    filter_upwards [hGa, (hgood x hx).2.2] with y hy hxy
    intro hn
    apply le_antisymm _ (bK (x,y)).1
    by_contra h
    exact hn ⟨hy, hxy (lt_of_not_ge h)⟩
  have hmC (x : Ω) : MeasurableSet (FourColorClasses.classSet G R x) :=
    hG.inter (FourColorRowDistance.measurable_twin_class μ H hH bH' x)
  have hpC (x : Ω) (hx : x ∈ G) :
      (1 / 6 : ℝ) ≤ μ.real (FourColorClasses.classSet G R x) :=
    TwoPairFiniteClasses.mass_of_supported_row μ _ (hmC x) _ (hi x)
      (hcap x hx) (hs x hx) (hgood x hx).2.1
  have he := FourColorRowDistance.twin_equivalence μ H
  have hpart := FourColorClasses.positive_equivalence_partition μ G R
    (fun x _ => he.refl x) (fun x _ y _ h => he.symm h)
    (fun x _ y _ z _ h h' => he.trans h h') (fun x _ => hmC x)
    (fun x hx => by
      have hh : 0 < μ.real (FourColorClasses.classSet G R x) := by linarith [hpC x hx]
      exact (ENNReal.toReal_pos_iff.mp hh).1)
  have hfin := TwoPairFiniteClasses.finite_twin_classes μ H K hH bH' G hG
    (fun x _ => hi x) hcap hs (fun x hx => (hgood x hx).2.1)
  exact ⟨G,hG,hGa,(fun x hx => ⟨hmC x,hpC x hx⟩),hfin.1,hfin.2,
    hpart.2.2.1,hpart.2.2.2⟩

end TwoPairClassExtraction
end


-- Local module: TwoPairFiniteReduction
section
open MeasureTheory
namespace TwoPairFiniteReduction
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def supportKernel (P : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  Set.indicator {q | 0 < P q} (fun _ => 1) p

lemma supportKernel_measurable (P : Ω × Ω → ℝ) (hP : Measurable P) :
    Measurable (supportKernel P) :=
  measurable_const.indicator (measurableSet_lt measurable_const hP)
lemma supportKernel_binary (P : Ω × Ω → ℝ) (p : Ω × Ω) :
    supportKernel P p=0 ∨ supportKernel P p=1 := by
  classical
  by_cases hp : 0 < P p <;> simp [supportKernel,hp]
lemma supportKernel_symm (P : Ω × Ω → ℝ) (sP : ∀ x y, P (x,y)=P (y,x)) (x y : Ω) :
    supportKernel P (x,y)=supportKernel P (y,x) := by
  classical
  simp only [supportKernel,Set.indicator_apply,Set.mem_setOf_eq,sP x y]

lemma act_comp (C D : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hC : Measurable C) (hD : Measurable D) (hf : Measurable f)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : Ω) :
    act μ (comp μ C D) f x=act μ C (act μ D f) x := by
  have hi : Integrable (fun p : Ω × Ω => C (x,p.1)*(D p*f p.2)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bC _) (mul_unit (bD _) (bf _)))
  calc
    _ = ∫ y, ∫ z, C (x,z)*(D (z,y)*f y) ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∫ z, C (x,z)*D (z,y) ∂μ)*f y = _
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by dsimp only; ring)
    _ = ∫ z, ∫ y, C (x,z)*(D (z,y)*f y) ∂μ ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => integral_const_mul _ _)

/-- Actual image orthogonality follows from independence under CD+DC. -/
lemma images_orthogonal
    (C D L : Ω × Ω → ℝ) (hC : Measurable C) (hD : Measurable D)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (eL : ∀ᵐ p ∂μ.prod μ, L p=comp μ C D p+comp μ D C p)
    (s : Ω → ℝ) (hs : Measurable s) (bs : ∀ x, s x=0 ∨ s x=1)
    (hind : ∀ᵐ p ∂μ.prod μ, s p.1=1 → s p.2=1 → L p=0) :
    (∫ x, act μ C s x*act μ D s x ∂μ)=0 := by
  have bu (x : Ω) : 0 ≤ s x ∧ s x ≤ 1 := by rcases bs x with h | h <;> simp [h]
  have hCD := measurable_comp μ C D hC hD
  have bCD := comp_bounds μ C D hC hD bC bD
  have hi : Integrable (fun p : Ω × Ω => s p.1*(comp μ C D p*s p.2)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (bu _) (mul_unit (bCD _) (bu _)))
  have hz : (fun p : Ω × Ω => s p.1*(comp μ C D p*s p.2)) =ᵐ[μ.prod μ] (fun _ => (0:ℝ)) := by
    filter_upwards [eL,hind] with p hp hpi
    rcases bs p.1 with h1 | h1 <;> rcases bs p.2 with h2 | h2
    · simp [h1,h2]
    · simp [h1,h2]
    · simp [h1,h2]
    · have hL0 := hpi h1 h2
      have hn := (comp_bounds μ D C hD hC bD bC p).1
      have hzero : comp μ C D p=0 := by linarith [(bCD p).1]
      simp [h1,h2,hzero]
  have hweighted : (∫ x, s x*act μ (comp μ C D) s x ∂μ)=0 := by
    have hh := integral_congr_ae hz
    rw [integral_prod _ hi] at hh
    have he : (∫ x, ∫ y, s x*(comp μ C D (x,y)*s y) ∂μ ∂μ)=
        ∫ x, s x*act μ (comp μ C D) s x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => integral_const_mul _ _)
    rw [he] at hh
    simpa using hh
  calc
    _ = ∫ x, act μ D s x*act μ C s x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
    _ = ∫ x, s x*act μ C (act μ D s) x ∂μ :=
      (act_pairing μ C s (act μ D s) hC hs (measurable_act μ D s hD hs)
        bC bu (act_bounds μ D s hD hs bD bu) sC).symm
    _ = ∫ x, s x*act μ (comp μ C D) s x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [act_comp μ C D s hC hD hs bC bD bu x])
    _ = 0 := hweighted

/-- Finite actual H-row classes follow from the composition hypotheses;
image orthogonality, half-set invariance and row confinement are all derived. -/
theorem finite_reduction
    (A B C D P L R : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L) (hR : Measurable R)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (bP : ∀ p, 0 ≤ P p ∧ P p ≤ 1) (bL : ∀ p, 0 ≤ L p ∧ L p ≤ 1)
    (bR : ∀ p, 0 ≤ R p ∧ R p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (sP : ∀ x y, P (x,y)=P (y,x)) (sL : ∀ x y, L (x,y)=L (y,x))
    (bQ : ∀ x z, 0 ≤ A (x,z)+B (x,z) ∧ A (x,z)+B (x,z) ≤ 1/2)
    (rQ : ∀ᵐ u ∂μ, ∫ z, (A (u,z)+B (u,z)) ∂μ = (1:ℝ)/3)
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6)
    (eP : ∀ᵐ p ∂μ.prod μ, P p=comp μ A B p+comp μ B A p)
    (eL : ∀ p, L p=comp μ C D p+comp μ D C p)
    (eR : ∀ p, R p=C p+D p)
    (eQ : ∀ᵐ p ∂μ.prod μ,
      comp μ (fun p => A p+B p) (fun p => A p+B p) p=(1:ℝ)/12+comp μ R R p/4)
    (hzA : ∀ᵐ p ∂μ.prod μ, comp μ A A p*L p=0)
    (hzB : ∀ᵐ p ∂μ.prod μ, comp μ B B p*L p=0)
    (hzP : ∀ᵐ p ∂μ.prod μ, comp μ P P p*L p=0) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ x ∂μ, x ∈ G) ∧
      let Rel := fun x y => (fun z => supportKernel P (x,z)) =ᵐ[μ] (fun z => supportKernel P (y,z))
      (∀ x ∈ G, MeasurableSet (FourColorClasses.classSet G Rel x) ∧
        (1 / 6 : ℝ) ≤ μ.real (FourColorClasses.classSet G Rel x)) ∧
      (FourColorClasses.classFamily G Rel).Finite ∧
      (FourColorClasses.classFamily G Rel).ncard ≤ 6 ∧
      (FourColorClasses.classFamily G Rel).PairwiseDisjoint id ∧
      ⋃₀ FourColorClasses.classFamily G Rel = G := by
  have rL : ∀ᵐ x ∂μ, ∫ y, L (x,y) ∂μ=(1:ℝ)/18 := by
    filter_upwards [comp_row μ C D hC hD bC bD (1/6) (1/6) rC rD,
      comp_row μ D C hD hC bD bC (1/6) (1/6) rD rC] with x hx hy
    have hiCD := unit_integrable μ (fun y => comp μ C D (x,y)) ((measurable_comp μ C D hC hD).comp (measurable_const.prodMk measurable_id))
      (fun y => comp_bounds μ C D hC hD bC bD (x,y))
    have hiDC := unit_integrable μ (fun y => comp μ D C (x,y)) ((measurable_comp μ D C hD hC).comp (measurable_const.prodMk measurable_id))
      (fun y => comp_bounds μ D C hD hC bD bC (x,y))
    simp_rw [eL]
    rw [integral_add hiCD hiDC,hx,hy]
    norm_num
  have hdom : ∀ᵐ p ∂μ.prod μ, L p ≤ comp μ R R p :=
    Filter.Eventually.of_forall (fun p => by
      rw [eL]
      exact TwoPairHalfSupportBridge.remainder_square_dom μ C D R hC hD hR bC bD bR eR p)
  have hhalf := TwoPairHalfSupportBridge.half_support_from_compositions μ A B P L R
    hA hB hP hL bA bB bP bL sA sB sP sL bQ rQ (1/18) (by norm_num) rL eP eQ hdom hzA hzB hzP
  have hind := (TwoPairHalfSupportBridge.independence_and_disjointness μ P L hP hL bP sP hzP).1
  have hH := supportKernel_measurable P hP
  have bH := supportKernel_binary P
  have sH := supportKernel_symm P sP
  have heigen : ∀ᵐ z ∂μ, ∀ᵐ x ∂μ,
      act μ (comp μ C C) (fun y => supportKernel P (z,y)) x=(1:ℝ)/36*supportKernel P (z,x) := by
    filter_upwards [hhalf,hind] with z hz hzi
    let S : Set Ω := {y | 0 < P (z,y)}
    have hS : MeasurableSet S := measurableSet_lt measurable_const
      (hP.comp (measurable_const.prodMk measurable_id))
    have hzind : ∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 → L p=0 := by
      filter_upwards [hzi] with p hp
      intro hx hy
      have hx' : 0 < P (z,p.1) := by by_contra hn; simp [oneSet,S,hn] at hx
      have hy' : 0 < P (z,p.2) := by by_contra hn; simp [oneSet,S,hn] at hy
      exact hp hx' hy'
    have him := images_orthogonal μ C D L hC hD bC bD sC
      (Filter.Eventually.of_forall eL) (oneSet S) (oneSet_measurable S hS) (oneSet_binary S) hzind
    have hsquare := half_set_square_preservation μ C D hC hD bC bD sC sD
      (1/6) (by norm_num) rC rD S hS hz him
    have he : oneSet S=(fun y => supportKernel P (z,y)) := by
      funext y
      by_cases hy : 0 < P (z,y) <;> simp [oneSet,supportKernel,S,hy]
    filter_upwards [hsquare] with x hx
    simpa only [he,show ((1:ℝ)/6)^2=1/36 by norm_num] using hx
  have rK : ∀ᵐ x ∂μ, ∫ y, comp μ C C (x,y) ∂μ=(1:ℝ)/36 := by
    simpa only [show ((1:ℝ)/6)*((1:ℝ)/6)=1/36 by norm_num] using
      comp_row μ C C hC hC bC bC (1/6) (1/6) rC rC
  have hconf := TwoPairRowConfinement.row_confinement μ (comp μ C C) (supportKernel P)
    (measurable_comp μ C C hC hC) hH (comp_bounds μ C C hC hC bC bC) bH sH
    (1/36) rK heigen
  exact TwoPairClassExtraction.extract_classes μ C (supportKernel P) hC hH bC bH rC hconf
end TwoPairFiniteReduction
end


-- Local module: TwoPairTwinRectangles
section
open MeasureTheory
namespace TwoPairTwinRectangles
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable function depending only on either coordinate of a positive
rectangle must be constant; one binary side makes the constant binary. -/
lemma separated_functions_constant
    (ν η : Measure Ω) [NeZero ν] [NeZero η]
    (f g : Ω → ℝ)
    (he : ∀ᵐ x ∂ν, ∀ᵐ y ∂η, f y=g x)
    (bg : ∀ᵐ x ∂ν, g x=0 ∨ g x=1) :
    ∃ b : ℝ, (b=0 ∨ b=1) ∧
      f =ᵐ[η] (fun _ => b) ∧ g =ᵐ[ν] (fun _ => b) := by
  obtain ⟨x,hx,hbx⟩ := (he.and bg).exists
  refine ⟨g x,hbx,hx,?_⟩
  filter_upwards [he] with z hz
  obtain ⟨y,hy,hxy⟩ := (hz.and hx).exists
  exact hy.symm.trans hxy

/-- Positive twin-row classes determine a single binary rectangle value.
Only the binary condition on fY is needed; no rectangle constancy is assumed. -/
theorem twin_rectangle_constant (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω × Ω → ℝ) (hH : Measurable H)
    (sH : ∀ x y, H (x,y)=H (y,x))
    (X Y : Set Ω) (pX : 0 < μ X) (pY : 0 < μ Y)
    (fX fY : Ω → ℝ) (hX : Measurable fX) (hY : Measurable fY)
    (bY : ∀ᵐ x ∂μ.restrict X, fY x=0 ∨ fY x=1)
    (rX : ∀ᵐ x ∂μ.restrict X, (fun z => H (x,z)) =ᵐ[μ] fX)
    (rY : ∀ᵐ y ∂μ.restrict Y, (fun z => H (y,z)) =ᵐ[μ] fY) :
    ∃ b : ℝ, (b=0 ∨ b=1) ∧
      H =ᵐ[(μ.restrict X).prod (μ.restrict Y)] (fun _ => b) ∧
      fX =ᵐ[μ.restrict Y] (fun _ => b) ∧
      fY =ᵐ[μ.restrict X] (fun _ => b) := by
  have hnX : μ.restrict X ≠ 0 := by
    intro hz
    have hm : μ X=0 := by simpa using congrArg (fun m : Measure Ω => m Set.univ) hz
    exact (ne_of_gt pX) hm
  have hnY : μ.restrict Y ≠ 0 := by
    intro hz
    have hm : μ Y=0 := by simpa using congrArg (fun m : Measure Ω => m Set.univ) hz
    exact (ne_of_gt pY) hm
  letI : NeZero (μ.restrict X) := ⟨hnX⟩
  letI : NeZero (μ.restrict Y) := ⟨hnY⟩
  have hrX : ∀ᵐ x ∂μ.restrict X, ∀ᵐ y ∂μ.restrict Y, H (x,y)=fX y := by
    filter_upwards [rX] with x hx
    exact ae_restrict_of_ae hx
  have hrY : ∀ᵐ x ∂μ.restrict X, ∀ᵐ y ∂μ.restrict Y, H (x,y)=fY x := by
    apply (Measure.ae_ae_comm (p := fun x y => H (x,y)=fY x) ?_).mpr
    · filter_upwards [rY] with y hy
      filter_upwards [ae_restrict_of_ae hy] with x hx
      simpa only [sH x] using hx
    · exact measurableSet_eq_fun hH (hY.comp measurable_fst)
  have hsep : ∀ᵐ x ∂μ.restrict X, ∀ᵐ y ∂μ.restrict Y, fX y=fY x := by
    filter_upwards [hrX,hrY] with x hx hy
    filter_upwards [hx,hy] with y hxy hyx
    exact hxy.symm.trans hyx
  obtain ⟨b,hb,hfx,hfy⟩ := separated_functions_constant (μ.restrict X) (μ.restrict Y)
    fX fY hsep bY
  refine ⟨b,hb,?_,hfx,hfy⟩
  have hrect : ∀ᵐ x ∂μ.restrict X, ∀ᵐ y ∂μ.restrict Y, H (x,y)=b := by
    filter_upwards [hrX] with x hx
    filter_upwards [hx,hfx] with y hy hfy
    exact hy.trans hfy
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hH measurable_const)).mpr hrect
end TwoPairTwinRectangles
end


-- Local module: TwoPairAntipodal
section

namespace TwoPairAntipodal

abbrev Vertex := Fin 3 × ZMod 2

def sign (a b c : ZMod 2) (i j : Fin 3) : ZMod 2 :=
  ![![0, a, b], ![a, 0, c], ![b, c, 0]] i j

/-- A binary antipodal relation specified by its three checkerboard signs. -/
def edge (a b c : ZMod 2) (u v : Vertex) : Prop :=
  if u.1 = v.1 then u.2 ≠ v.2 else u.2 + v.2 = sign a b c u.1 v.1

def uniform (t : ZMod 2) (u v : Vertex) : Prop :=
  if u.1 = v.1 then u.2 ≠ v.2 else u.2 + v.2 = t

def prism (u v : Vertex) : Prop :=
  (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.1 ≠ v.1 ∧ u.2 = v.2)

def switch (s : Fin 3 → ZMod 2) (u : Vertex) : Vertex :=
  (u.1, u.2 + s u.1)

def normalizingShift (a b c : ZMod 2) : Fin 3 → ZMod 2 :=
  ![0, a + (a + b + c), b + (a + b + c)]

private theorem add_twice (a b : ZMod 2) : (a + b) + b = a := by
  revert a b; decide

theorem switch_involutive (s : Fin 3 → ZMod 2) : Function.Involutive (switch s) := by
  intro u
  apply Prod.ext
  · rfl
  · exact add_twice u.2 (s u.1)

/-- Switching all three pair coordinates normalizes every checkerboard sign. -/
theorem normalize (a b c : ZMod 2) :
    ∀ u v : Vertex,
      edge a b c (switch (normalizingShift a b c) u)
        (switch (normalizingShift a b c) v) ↔ uniform (a + b + c) u v := by
  unfold edge uniform switch normalizingShift sign
  revert a b c
  decide

theorem uniform_zero : ∀ u v : Vertex, uniform 0 u v ↔ prism u v := by unfold uniform prism; decide

theorem uniform_one : ∀ u v : Vertex, uniform 1 u v ↔ u.2 ≠ v.2 := by unfold uniform; decide

/-- Every signed three-pair relation is a switched bipartite graph or prism. -/
theorem three_pair_classification (a b c : ZMod 2) :
    ∃ s : Fin 3 → ZMod 2,
      (∀ u v : Vertex, edge a b c (switch s u) (switch s v) ↔ u.2 ≠ v.2) ∨
      (∀ u v : Vertex, edge a b c (switch s u) (switch s v) ↔ prism u v) := by
  refine ⟨normalizingShift a b c, ?_⟩
  have ht : a + b + c = 0 ∨ a + b + c = 1 := by
    have h : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    exact h (a + b + c)
  rcases ht with ht | ht
  · right
    intro u v
    exact (normalize a b c u v).trans (by rw [ht]; exact uniform_zero u v)
  · left
    intro u v
    exact (normalize a b c u v).trans (by rw [ht]; exact uniform_one u v)


end TwoPairAntipodal
end


-- Local module: TwoPairAntipodalQuotient
section
namespace TwoPairAntipodalQuotient
variable {I : Type*}

lemma column_complement (H : I → I → Bool) (τ : I → I)
    (hs : ∀ i j, H i j = H j i)
    (hc : ∀ i j, H (τ i) j = !(H i j)) (i j : I) :
    H i (τ j) = !(H i j) := by rw [hs, hc, hs j i]

/-- Two antipodal pairs yield duplicate rows unless they are the same pair. -/
theorem two_pair_cover_collapse (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hd : ∀ i, H i i = false)
    (hc : ∀ i j, H (τ i) j = !(H i j))
    (hinj : Function.Injective (fun i => H i)) (a b : I)
    (hcover : ∀ j, j = a ∨ j = τ a ∨ j = b ∨ j = τ b) :
    b = a ∨ b = τ a := by
  have col := column_complement H τ hs hc
  have same (x y : I) (hxy : H x y = false)
      (cover : ∀ j, j = x ∨ j = τ x ∨ j = y ∨ j = τ y) : x = y := by
    apply hinj
    funext j
    change H x j = H y j
    rcases cover j with rfl | rfl | rfl | rfl
    · rw [hd, hs, hxy]
    · rw [col, col, hd, hs y x, hxy]
    · rw [hxy, hd]
    · rw [col, col, hxy, hd]
  cases hab : H a b with
  | false => exact Or.inl (same a b hab hcover).symm
  | true =>
    have hzero : H a (τ b) = false := by rw [col,hab]; rfl
    have cover : ∀ j, j = a ∨ j = τ a ∨ j = τ b ∨ j = τ (τ b) := by
      intro j
      simpa only [ht b, or_comm, or_left_comm, or_assoc] using hcover j
    have he := congrArg τ (same a (τ b) hzero cover)
    exact Or.inr (by simpa only [ht b] using he.symm)

/-- Exactly four distinct rows are impossible under an antipodal involution. -/
theorem card_ne_four [Fintype I] (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hn : ∀ i, τ i ≠ i)
    (hs : ∀ i j, H i j = H j i) (hd : ∀ i, H i i = false)
    (hc : ∀ i j, H (τ i) j = !(H i j))
    (hinj : Function.Injective (fun i => H i)) : Fintype.card I ≠ 4 := by
  classical
  intro hcard
  have hpos : 0 < Fintype.card I := by omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
  have hnot : ¬ (Finset.univ : Finset I) ⊆ {a,τ a} := by
    intro h
    have hh := Finset.card_le_card h
    have hu : (Finset.univ : Finset I).card = 4 := hcard
    simp only [Finset.card_univ] at hh
    have hp' : ({a,τ a} : Finset I).card = 2 := by simp [hn a, Ne.symm (hn a)]
    omega
  obtain ⟨b,_,hb⟩ := Finset.not_subset.mp hnot
  have hba : b ≠ a := by intro h; exact hb (by simp [h])
  have hbt : b ≠ τ a := by intro h; exact hb (by simp [h])
  have htba : τ b ≠ a := by intro h; exact hbt (by simpa only [ht b] using congrArg τ h)
  have htbt : τ b ≠ τ a := ht.injective.ne hba
  have hsize : ({a,τ a,b,τ b} : Finset I).card = 4 := by
    simp [hn a, hn b, hba, hbt, htba, htbt, Ne.symm (hn a),
      Ne.symm (hn b), Ne.symm hba, Ne.symm hbt, Ne.symm htba, Ne.symm htbt]
  have hu : ({a,τ a,b,τ b} : Finset I) = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp (hsize.trans hcard.symm)
  have cover : ∀ j, j = a ∨ j = τ a ∨ j = b ∨ j = τ b := by
    intro j
    have hj : j ∈ ({a,τ a,b,τ b} : Finset I) := by rw [hu]; exact Finset.mem_univ j
    simpa using hj
  exact (two_pair_cover_collapse H τ ht hs hd hc hinj a b cover).elim hba hbt

/-- The partner involution pairs the two values of any fixed row. -/
theorem even_card [Fintype I] (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hc : ∀ i j, H (τ i) j = !(H i j)) (a : I) : Even (Fintype.card I) := by
  classical
  have col := column_complement H τ hs hc
  let e : {j // H a j = true} ≃ {j // ¬ H a j = true} :=
    { toFun := fun j => ⟨τ j.val, by rw [col, j.property]; decide⟩
      invFun := fun j => ⟨τ j.val, by
        rw [col]
        have hj := j.property
        cases h : H a j.val <;> simp_all⟩
      left_inv := fun j => Subtype.ext (ht j.val)
      right_inv := fun j => Subtype.ext (ht j.val) }
  have he := Fintype.card_congr e
  rw [Fintype.card_subtype_compl] at he
  exact ⟨Fintype.card {j // H a j = true}, by omega⟩

/-- At most six distinct antipodal rows leave exactly two or six indices. -/
theorem card_two_or_six [Fintype I] [Nonempty I]
    (H : I → I → Bool) (τ : I → I)
    (hsize : Fintype.card I ≤ 6)
    (ht : Function.Involutive τ) (hn : ∀ i, τ i ≠ i)
    (hs : ∀ i j, H i j = H j i) (hd : ∀ i, H i i = false)
    (hc : ∀ i j, H (τ i) j = !(H i j))
    (hinj : Function.Injective (fun i => H i)) :
    Fintype.card I = 2 ∨ Fintype.card I = 6 := by
  obtain ⟨a⟩ := ‹Nonempty I›
  obtain ⟨k,hk⟩ := even_card H τ ht hs hc a
  have hfour := card_ne_four H τ ht hn hs hd hc hinj
  have hpos := Fintype.card_pos_iff.mpr (show Nonempty I from ⟨a⟩)
  omega

end TwoPairAntipodalQuotient
end


-- Local module: TwoPairAntipodalCoordinates
section

namespace TwoPairAntipodalCoordinates
variable {I : Type*}

abbrev Rep (H : I → I → Bool) (a : I) := {i // H a i = false}

def orient (τ : I → I) {H : I → I → Bool} {a : I} (p : Rep H a × Bool) : I :=
  if p.2 then τ p.1.val else p.1.val

noncomputable def representativeEquiv (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hc : ∀ i j, H (τ i) j = !(H i j)) (a : I) :
    (Rep H a × Bool) ≃ I := by
  have col := TwoPairAntipodalQuotient.column_complement H τ hs hc
  apply Equiv.ofBijective (orient τ)
  constructor
  · rintro ⟨⟨x,hx⟩,bx⟩ ⟨⟨y,hy⟩,by'⟩ he
    cases bx <;> cases by'
    · have h : x = y := he
      subst y
      rfl
    · have h : x = τ y := he
      have hz := congrArg (H a) h
      rw [col,hx,hy] at hz
      contradiction
    · have h : τ x = y := he
      have hz := congrArg (H a) h
      rw [col,hx,hy] at hz
      contradiction
    · have h : x = y := ht.injective he
      subst y
      rfl
  · intro i
    cases hi : H a i with
    | false => exact ⟨⟨⟨i,hi⟩,false⟩,rfl⟩
    | true =>
      have hrep : H a (τ i) = false := by rw [col,hi]; rfl
      exact ⟨⟨⟨τ i,hrep⟩,true⟩,ht i⟩

lemma representativeEquiv_flip (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hc : ∀ i j, H (τ i) j = !(H i j)) (a : I)
    (i : Rep H a) (b : Bool) :
    representativeEquiv H τ ht hs hc a (i,!b) =
      τ (representativeEquiv H τ ht hs hc a (i,b)) := by
  cases b
  · rfl
  · exact (ht i.val).symm

/-- A false row fiber supplies exactly three representatives when there are six indices. -/
theorem representatives_card [Fintype I] (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hc : ∀ i j, H (τ i) j = !(H i j)) (a : I)
    (hn : Fintype.card I = 6) : Fintype.card (Rep H a) = 3 := by
  classical
  have he := Fintype.card_congr (representativeEquiv H τ ht hs hc a)
  simp only [Fintype.card_prod, Fintype.card_bool, hn] at he
  omega

/-- Coordinates intertwine Boolean bit flip with the actual partner involution. -/
theorem exists_coordinates [Fintype I] (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hc : ∀ i j, H (τ i) j = !(H i j)) (a : I)
    (hn : Fintype.card I = 6) :
    ∃ e : (Fin 3 × Bool) ≃ I, ∀ i b, e (i,!b) = τ (e (i,b)) := by
  classical
  let r : Fin 3 ≃ Rep H a :=
    (Fintype.equivFinOfCardEq (representatives_card H τ ht hs hc a hn)).symm
  let e := (Equiv.prodCongr r (Equiv.refl Bool)).trans (representativeEquiv H τ ht hs hc a)
  refine ⟨e,?_⟩
  intro i b
  exact representativeEquiv_flip H τ ht hs hc a (r i) b

def bitBoolEquiv : ZMod 2 ≃ Bool where
  toFun b := decide (b = 1)
  invFun b := if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

lemma bitBoolEquiv_flip : ∀ b : ZMod 2,
    bitBoolEquiv (b + 1) = !(bitBoolEquiv b) := by decide

theorem exists_zmod_coordinates [Fintype I] (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hc : ∀ i j, H (τ i) j = !(H i j)) (a : I)
    (hn : Fintype.card I = 6) :
    ∃ e : (Fin 3 × ZMod 2) ≃ I, ∀ i b, e (i,b+1) = τ (e (i,b)) := by
  obtain ⟨e,he⟩ := exists_coordinates H τ ht hs hc a hn
  refine ⟨(Equiv.prodCongr (Equiv.refl (Fin 3)) bitBoolEquiv).trans e,?_⟩
  intro i b
  change e (i,bitBoolEquiv (b+1)) = τ (e (i,bitBoolEquiv b))
  rw [bitBoolEquiv_flip]
  exact he i (bitBoolEquiv b)

end TwoPairAntipodalCoordinates
end


-- Local module: TwoPairAntipodalClassification
section

namespace TwoPairAntipodalClassification
open TwoPairAntipodal
variable {I : Type*}

def encode (b : Bool) : ZMod 2 := if b then 0 else 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma finite_sign_table (base : Fin 3 → Fin 3 → Bool)
    (diag : ∀ i, base i i = false) (sym : ∀ i j, base i j = base j i)
    (i j : Fin 3) (b d : ZMod 2) :
    (if b = 0 then (if d = 0 then base i j else !(base i j))
      else (if d = 0 then !(base i j) else base i j)) = true ↔
      edge (encode (base 0 1)) (encode (base 0 2)) (encode (base 1 2)) (i,b) (j,d) := by
  revert i j b d
  revert diag sym
  revert base
  unfold edge sign encode
  decide

theorem pullback_edge (H : I → I → Bool) (τ : I → I)
    (hs : ∀ i j, H i j = H j i) (hd : ∀ i, H i i = false)
    (hc : ∀ i j, H (τ i) j = !(H i j))
    (e : Vertex ≃ I) (he : ∀ i b, e (i,b+1) = τ (e (i,b))) :
    let a := encode (H (e (0,0)) (e (1,0)))
    let b := encode (H (e (0,0)) (e (2,0)))
    let c := encode (H (e (1,0)) (e (2,0)))
    ∀ u v : Vertex, H (e u) (e v) = true ↔ edge a b c u v := by
  let base (i j : Fin 3) := H (e (i,0)) (e (j,0))
  have hleft (i j : Fin 3) (d : ZMod 2) :
      H (e (i,1)) (e (j,d)) = !(H (e (i,0)) (e (j,d))) := by
    rw [show (1 : ZMod 2) = 0+1 by simp,he,hc]
  have hright (i j : Fin 3) :
      H (e (i,0)) (e (j,1)) = !(base i j) := by
    rw [hs, hleft, hs (e (j,0)) (e (i,0))]
  have form (i j : Fin 3) (b d : ZMod 2) :
      H (e (i,b)) (e (j,d)) =
        if b = 0 then (if d = 0 then base i j else !(base i j))
        else (if d = 0 then !(base i j) else base i j) := by
    have bits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases bits b with rfl | rfl <;> rcases bits d with rfl | rfl
    · simp [base]
    · simpa using hright i j
    · simpa [base] using hleft i j 0
    · simp [hleft,hright]
  have diag (i : Fin 3) : base i i = false := hd _
  have sym (i j : Fin 3) : base i j = base j i := hs _ _
  dsimp only
  rintro ⟨i,b⟩ ⟨j,d⟩
  rw [form]
  change (if b = 0 then (if d = 0 then base i j else !(base i j))
    else (if d = 0 then !(base i j) else base i j)) = true ↔ _
  exact finite_sign_table base diag sym i j b d

/-- Every six-class antipodal quotient is isomorphic to K3,3 or the prism. -/
theorem classify_six [Fintype I] [Nonempty I]
    (H : I → I → Bool) (τ : I → I)
    (ht : Function.Involutive τ) (hs : ∀ i j, H i j = H j i)
    (hd : ∀ i, H i i = false)
    (hc : ∀ i j, H (τ i) j = !(H i j))
    (hn : Fintype.card I = 6) :
    ∃ e : Vertex ≃ I,
      (∀ u v, H (e u) (e v) = true ↔ u.2 ≠ v.2) ∨
      (∀ u v, H (e u) (e v) = true ↔ prism u v) := by
  obtain ⟨root⟩ := ‹Nonempty I›
  obtain ⟨e,he⟩ := TwoPairAntipodalCoordinates.exists_zmod_coordinates H τ ht hs hc root hn
  let a := encode (H (e (0,0)) (e (1,0)))
  let b := encode (H (e (0,0)) (e (2,0)))
  let c := encode (H (e (1,0)) (e (2,0)))
  have hp := pullback_edge H τ hs hd hc e he
  obtain ⟨s,hswitch⟩ := three_pair_classification a b c
  let f : Vertex ≃ Vertex :=
    { toFun := switch s
      invFun := switch s
      left_inv := switch_involutive s
      right_inv := switch_involutive s }
  refine ⟨f.trans e,?_⟩
  rcases hswitch with h | h
  · left
    intro u v
    exact (hp (switch s u) (switch s v)).trans (h u v)
  · right
    intro u v
    exact (hp (switch s u) (switch s v)).trans (h u v)

end TwoPairAntipodalClassification
end


-- Local module: TwoPairPartnerMass
section
open MeasureTheory
namespace TwoPairPartnerMass
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def one (S : Set Ω) : Ω → ℝ := S.indicator (fun _ => 1)

lemma one_bounds (S : Set Ω) (x : Ω) : 0 ≤ one S x ∧ one S x ≤ 1 := by
  classical
  by_cases hx : x ∈ S <;> simp [one,hx]

lemma flow_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω × Ω → ℝ) (d : ℝ)
    (bK : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p)
    (hr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ = d)
    (X Y : Set Ω) (hX : MeasurableSet X)
    (hxy : ∀ᵐ p ∂μ.prod μ, p.1 ∈ X → 0 < K p → p.2 ∈ Y) :
    (∫ x, ∫ y, one X x * (K (x,y) * one Y y) ∂μ ∂μ) = μ.real X * d := by
  classical
  calc
    _ = ∫ x, X.indicator (fun _ => d) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hr,Measure.ae_ae_of_ae_prod bK,Measure.ae_ae_of_ae_prod hxy] with x hx hb he
      by_cases hxX : x ∈ X
      · have hrow : (∫ y, K (x,y) * one Y y ∂μ) = d := by
          rw [← hx]
          apply integral_congr_ae
          filter_upwards [hb,he] with y hy hy'
          by_cases hyY : y ∈ Y
          · simp [one,hyY]
          · have hz : K (x,y) = 0 := by
              apply le_antisymm _ hy
              by_contra h
              exact hyY (hy' hxX (lt_of_not_ge h))
            simp [hz]
        simpa [one,hxX] using hrow
      · simp [one,hxX]
    _ = μ.real X * d := by rw [integral_indicator_const d hX]; rfl

/-- Symmetric flow confined in both directions equates the two masses. -/
theorem partner_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω × Ω → ℝ) (hK : Measurable K)
    (bK : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p ∧ K p ≤ 1)
    (sK : ∀ᵐ p ∂μ.prod μ, K p = K (p.2,p.1))
    (d : ℝ) (hd : 0 < d)
    (hr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ = d)
    (X Y : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hxy : ∀ᵐ p ∂μ.prod μ, p.1 ∈ X → 0 < K p → p.2 ∈ Y)
    (hyx : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Y → 0 < K p → p.2 ∈ X) :
    μ.real X = μ.real Y := by
  have hx : Measurable (one X) := measurable_const.indicator hX
  have hy : Measurable (one Y) := measurable_const.indicator hY
  have hi : Integrable (fun p : Ω × Ω => one X p.1 * (K p * one Y p.2)) (μ.prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [bK] with p hp
    have hb := FourColorKernels.mul_unit (one_bounds X p.1)
      (FourColorKernels.mul_unit hp (one_bounds Y p.2))
    simpa only [Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2
  have he : (∫ x, ∫ y, one X x * (K (x,y) * one Y y) ∂μ ∂μ) =
      ∫ y, ∫ x, one Y y * (K (y,x) * one X x) ∂μ ∂μ := by
    rw [integral_integral_swap hi]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod sK] with y hyK
    apply integral_congr_ae
    filter_upwards [hyK] with x hxK
    rw [← hxK]
    ring
  rw [flow_mass μ K d (bK.mono (fun _ h => h.1)) hr X Y hX hxy,
    flow_mass μ K d (bK.mono (fun _ h => h.1)) hr Y X hY hyx] at he
  exact mul_right_cancel₀ hd.ne' he

end TwoPairPartnerMass
end


-- Local module: TwoPairSupportClassification
section

open MeasureTheory
namespace TwoPairSupportClassification
variable {Ω : Type*} [MeasurableSpace Ω]

def Twin (μ : Measure Ω) (H : Ω × Ω → ℝ) (x y : Ω) : Prop :=
  (fun z => H (x,z)) =ᵐ[μ] (fun z => H (y,z))

/-- The quotient index is exactly the family supplied by finite reduction. -/
abbrev Class (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω) :=
  ↥(FourColorClasses.classFamily G (Twin μ H))

noncomputable def representative (μ : Measure Ω) (H : Ω × Ω → ℝ)
    (G : Set Ω) (i : Class μ H G) : Ω := Classical.choose i.property

lemma representative_mem (μ : Measure Ω) (H : Ω × Ω → ℝ)
    (G : Set Ω) (i : Class μ H G) : representative μ H G i ∈ G :=
  (Classical.choose_spec i.property).1

lemma class_eq (μ : Measure Ω) (H : Ω × Ω → ℝ)
    (G : Set Ω) (i : Class μ H G) :
    i.val = FourColorClasses.classSet G (Twin μ H) (representative μ H G i) :=
  (Classical.choose_spec i.property).2

lemma row_on_class (μ : Measure Ω) (H : Ω × Ω → ℝ)
    (G : Set Ω) (i : Class μ H G) (hi : MeasurableSet i.val) :
    ∀ᵐ x ∂μ.restrict i.val,
      (fun z => H (x,z)) =ᵐ[μ] (fun z => H (representative μ H G i,z)) := by
  filter_upwards [ae_restrict_mem hi] with x hx
  rw [class_eq μ H G i] at hx
  exact hx.2.symm

/-- No block constancy is imposed: it follows from positive twin classes,
symmetry, and binary rows. The representatives need not be regularity-good. -/
theorem class_rectangle (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω × Ω → ℝ) (hm : Measurable H)
    (hb : ∀ p, H p=0 ∨ H p=1)
    (hs : ∀ x y, H (x,y)=H (y,x)) (G : Set Ω)
    (i j : Class μ H G)
    (mi : MeasurableSet i.val) (mj : MeasurableSet j.val)
    (pi : 0 < μ i.val) (pj : 0 < μ j.val) :
    ∃ b : ℝ, (b=0 ∨ b=1) ∧
      H =ᵐ[(μ.restrict i.val).prod (μ.restrict j.val)] (fun _ => b) ∧
      (fun z => H (representative μ H G i,z)) =ᵐ[μ.restrict j.val] (fun _ => b) ∧
      (fun z => H (representative μ H G j,z)) =ᵐ[μ.restrict i.val] (fun _ => b) := by
  apply TwoPairTwinRectangles.twin_rectangle_constant μ H hm hs i.val j.val pi pj
    (fun z => H (representative μ H G i,z))
    (fun z => H (representative μ H G j,z))
  · exact hm.comp (measurable_const.prodMk measurable_id)
  · exact hm.comp (measurable_const.prodMk measurable_id)
  · exact Filter.Eventually.of_forall (fun x => hb _)
  · exact row_on_class μ H G i mi
  · exact row_on_class μ H G j mj

/-- A faithful binary block table exists for the actual twin-class subtype.
The equality on profiles is retained for proving row injectivity and partners. -/
theorem exists_block_table (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω × Ω → ℝ) (hm : Measurable H)
    (hb : ∀ p, H p=0 ∨ H p=1)
    (hs : ∀ x y, H (x,y)=H (y,x)) (G : Set Ω)
    (hc : ∀ i : Class μ H G, MeasurableSet i.val ∧ 0 < μ i.val) :
    ∃ B : Class μ H G → Class μ H G → Bool,
      ∀ i j,
      H =ᵐ[(μ.restrict i.val).prod (μ.restrict j.val)]
        (fun _ => if B i j then (1:ℝ) else 0) ∧
      (fun z => H (representative μ H G i,z)) =ᵐ[μ.restrict j.val]
        (fun _ => if B i j then (1:ℝ) else 0) ∧
      (fun z => H (representative μ H G j,z)) =ᵐ[μ.restrict i.val]
        (fun _ => if B i j then (1:ℝ) else 0) := by
  classical
  have hh := fun i j => class_rectangle μ H hm hb hs G i j
    (hc i).1 (hc j).1 (hc i).2 (hc j).2
  choose b bb hrect hrow hcol using hh
  refine ⟨fun i j => decide (b i j=1), ?_⟩
  intro i j
  have he : (if decide (b i j=1) then (1:ℝ) else 0) = b i j := by
    rcases bb i j with h | h <;> simp [h]
  simpa only [he] using And.intro (hrect i j) (And.intro (hrow i j) (hcol i j))

lemma restricted_constants_unique (μ : Measure Ω) (X : Set Ω) (hp : 0 < μ X)
    (f : Ω → ℝ) (a b : ℝ)
    (ha : f =ᵐ[μ.restrict X] (fun _ => a))
    (hb : f =ᵐ[μ.restrict X] (fun _ => b)) : a=b := by
  have hn : μ.restrict X ≠ 0 := by
    intro hz
    have hm : μ X=0 := by
      simpa using congrArg (fun m : Measure Ω => m Set.univ) hz
    exact (ne_of_gt hp) hm
  letI : NeZero (μ.restrict X) := ⟨hn⟩
  obtain ⟨x,hx,hy⟩ := (ha.and hb).exists
  exact hx.symm.trans hy

lemma block_table_symmetric (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    (B : Class μ H G → Class μ H G → Bool)
    (hp : ∀ i : Class μ H G, 0 < μ i.val)
    (hr : ∀ i j, (fun z => H (representative μ H G i,z)) =ᵐ[μ.restrict j.val]
      (fun _ => if B i j then (1:ℝ) else 0))
    (hc : ∀ i j, (fun z => H (representative μ H G j,z)) =ᵐ[μ.restrict i.val]
      (fun _ => if B i j then (1:ℝ) else 0)) :
    ∀ i j, B i j=B j i := by
  intro i j
  have he := restricted_constants_unique μ i.val (hp i)
    (fun z => H (representative μ H G j,z)) _ _ (hc i j) (hr j i)
  cases hi : B i j <;> cases hj : B j i <;> simp_all

/-- Agreement on every positive class gives global almost-everywhere agreement.
This explicitly uses the conull cover and finiteness supplied by reduction. -/
lemma ae_of_classes (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    [Fintype (Class μ H G)]
    (hG : ∀ᵐ x ∂μ, x∈G)
    (hm : ∀ i : Class μ H G, MeasurableSet i.val)
    (P : Ω → Prop) (hp : ∀ i : Class μ H G, ∀ᵐ x ∂μ.restrict i.val, P x) :
    ∀ᵐ x ∂μ, P x := by
  have hall : ∀ᵐ x ∂μ, ∀ i : Class μ H G, x∈i.val → P x := by
    exact (ae_all_iff.mpr (fun i => (ae_restrict_iff' (hm i)).mp (hp i)))
  filter_upwards [hG,hall] with x hx hh
  let i : Class μ H G := ⟨FourColorClasses.classSet G (Twin μ H) x, x,hx,rfl⟩
  exact hh i ⟨hx,Filter.EventuallyEq.rfl⟩

lemma block_table_injective (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    [Fintype (Class μ H G)]
    (hG : ∀ᵐ x ∂μ, x∈G)
    (hm : ∀ i : Class μ H G, MeasurableSet i.val)
    (B : Class μ H G → Class μ H G → Bool)
    (hr : ∀ i j, (fun z => H (representative μ H G i,z)) =ᵐ[μ.restrict j.val]
      (fun _ => if B i j then (1:ℝ) else 0)) :
    Function.Injective (fun i => B i) := by
  intro i j hij
  change B i = B j at hij
  have he : Twin μ H (representative μ H G i) (representative μ H G j) := by
    apply ae_of_classes μ H G hG hm
    intro k
    have hh := hr j k
    rw [← hij] at hh
    exact (hr i k).trans hh.symm
  apply Subtype.ext
  rw [class_eq μ H G i, class_eq μ H G j]
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, he.symm.trans hz.2⟩
  · intro hz
    exact ⟨hz.1, he.trans hz.2⟩

lemma positive_integral_good_point (μ : Measure Ω) (f : Ω → ℝ)
    (hpos : 0 < ∫ x, f x ∂μ) (P : Ω → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ 0 < f x := by
  by_contra hn
  have hf : ∀ᵐ x ∂μ, f x ≤ 0 := by
    filter_upwards [hP] with x hx
    exact le_of_not_gt (fun h => hn ⟨x,hx,h⟩)
  exact (not_lt_of_ge (integral_nonpos_of_ae hf)) hpos

/-- Positive regular transport selects an actual complementary row class.
The chosen class representative itself need not be a good transport root. -/
lemma exists_complementary_class (μ : Measure Ω)
    (H L : Ω × Ω → ℝ) (G : Set Ω)
    (hG : ∀ᵐ x ∂μ, x∈G)
    (hm : ∀ i : Class μ H G, MeasurableSet i.val)
    (hp : ∀ i : Class μ H G, 0 < μ i.val)
    (hL : ∀ᵐ x ∂μ, 0 < ∫ y, L (x,y) ∂μ)
    (hcomp : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      (fun z => H (x,z)) =ᵐ[μ] (fun z => 1-H (y,z))) :
    ∀ i : Class μ H G, ∃ j : Class μ H G,
      (fun z => H (representative μ H G i,z)) =ᵐ[μ]
        (fun z => 1-H (representative μ H G j,z)) := by
  intro i
  have hn : μ.restrict i.val ≠ 0 := by
    intro hz
    have hz' : μ i.val=0 := by
      simpa using congrArg (fun m : Measure Ω => m Set.univ) hz
    exact (ne_of_gt (hp i)) hz'
  letI : NeZero (μ.restrict i.val) := ⟨hn⟩
  obtain ⟨x,hxr,hxl,hxc⟩ :=
    ((row_on_class μ H G i (hm i)).and
      ((ae_restrict_of_ae hL).and (ae_restrict_of_ae hcomp))).exists
  obtain ⟨y,⟨hyG,hyc⟩,hxy⟩ := positive_integral_good_point μ
    (fun y => L (x,y)) hxl _ (hG.and hxc)
  let j : Class μ H G := ⟨FourColorClasses.classSet G (Twin μ H) y,y,hyG,rfl⟩
  have hyj : y ∈ j.val := ⟨hyG,Filter.EventuallyEq.rfl⟩
  rw [class_eq μ H G j] at hyj
  refine ⟨j,?_⟩
  filter_upwards [hxr,hyc hxy,hyj.2] with z hz hzc hzy
  linarith

lemma complementary_table_rows (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    (B : Class μ H G → Class μ H G → Bool)
    (hp : ∀ i : Class μ H G, 0 < μ i.val)
    (hr : ∀ i j, (fun z => H (representative μ H G i,z)) =ᵐ[μ.restrict j.val]
      (fun _ => if B i j then (1:ℝ) else 0))
    (i j : Class μ H G)
    (he : (fun z => H (representative μ H G i,z)) =ᵐ[μ]
      (fun z => 1-H (representative μ H G j,z))) :
    ∀ k, B j k = !(B i k) := by
  intro k
  have hh : (fun z => H (representative μ H G i,z)) =ᵐ[μ.restrict k.val]
      (fun _ => 1-(if B j k then (1:ℝ) else 0)) := by
    filter_upwards [ae_restrict_of_ae he,hr j k] with z hz hj
    rw [hz,hj]
  have hnum := restricted_constants_unique μ k.val (hp k) _ _ _ (hr i k) hh
  cases hi : B i k <;> cases hj : B j k <;> simp_all

/-- Distinct binary rows make the complementary partner unique, involutive,
and fixed-point free. This is purely algebraic after measurable extraction. -/
lemma partner_involution {I : Type*} [Nonempty I] (B : I → I → Bool)
    (hinj : Function.Injective (fun i => B i))
    (τ : I → I) (hc : ∀ i k, B (τ i) k = !(B i k)) :
    Function.Involutive τ ∧ (∀ i, τ i ≠ i) := by
  constructor
  · intro i
    apply hinj
    funext k
    change B (τ (τ i)) k = B i k
    rw [hc,hc]
    simp
  · intro i he
    obtain ⟨k⟩ := ‹Nonempty I›
    have hh := hc i k
    rw [he] at hh
    cases h : B i k <;> simp_all

lemma member_row (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    (i : Class μ H G) {x : Ω} (hx : x ∈ i.val) :
    Twin μ H (representative μ H G i) x := by
  rw [class_eq μ H G i] at hx
  exact hx.2

lemma class_eq_of_profiles (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    (i j : Class μ H G)
    (he : Twin μ H (representative μ H G i) (representative μ H G j)) : i=j := by
  apply Subtype.ext
  rw [class_eq μ H G i,class_eq μ H G j]
  ext z
  constructor
  · intro hz
    exact ⟨hz.1,he.symm.trans hz.2⟩
  · intro hz
    exact ⟨hz.1,he.trans hz.2⟩

/-- Any complementary edge from a class must end in its selected partner.
This pointwise implication is applied only on the jointly a.e. good edges. -/
lemma complementary_edge_partner (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    (i j k : Class μ H G) {x y : Ω} (hx : x∈i.val) (hy : y∈j.val)
    (hik : (fun z => H (representative μ H G i,z)) =ᵐ[μ]
      (fun z => 1-H (representative μ H G k,z)))
    (hxy : (fun z => H (x,z)) =ᵐ[μ] (fun z => 1-H (y,z))) : j=k := by
  apply class_eq_of_profiles μ H G j k
  filter_upwards [member_row μ H G i hx,member_row μ H G j hy,hik,hxy]
    with z hiz hjz hikz hxyz
  linarith

lemma transport_confined_to_partner (μ : Measure Ω) [SFinite μ]
    (H L : Ω × Ω → ℝ) (G : Set Ω) (hL : Measurable L)
    (hG : ∀ᵐ x ∂μ, x∈G)
    (hm : ∀ i : Class μ H G, MeasurableSet i.val)
    (τ : Class μ H G → Class μ H G)
    (ht : ∀ i, (fun z => H (representative μ H G i,z)) =ᵐ[μ]
      (fun z => 1-H (representative μ H G (τ i),z)))
    (hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < L (x,y) →
      (fun z => H (x,z)) =ᵐ[μ] (fun z => 1-H (y,z))) :
    ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈i.val → 0<L p → p.2∈(τ i).val := by
  intro i
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [hc] with x hx
    filter_upwards [hG,hx] with y hy hxy
    intro hxi hl
    let j : Class μ H G := ⟨FourColorClasses.classSet G (Twin μ H) y,y,hy,rfl⟩
    have hyj : y∈j.val := ⟨hy,Filter.EventuallyEq.rfl⟩
    have he := complementary_edge_partner μ H G i j (τ i) hxi hyj (ht i) (hxy hl)
    simpa only [he] using hyj
  · convert ((hm i).preimage measurable_fst).compl.union
      ((measurableSet_lt (measurable_const : Measurable (fun _ : Ω × Ω => (0:ℝ))) hL).compl.union
        ((hm (τ i)).preimage measurable_snd)) using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage]
    tauto

lemma equal_partner_masses (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H L : Ω × Ω → ℝ) (G : Set Ω) (hL : Measurable L)
    (bL : ∀ᵐ p ∂μ.prod μ, 0≤L p ∧ L p≤1)
    (sL : ∀ᵐ p ∂μ.prod μ, L p=L (p.2,p.1))
    (d : ℝ) (hd : 0<d) (hr : ∀ᵐ x ∂μ, ∫ y,L (x,y) ∂μ=d)
    (hG : ∀ᵐ x ∂μ, x∈G)
    (hm : ∀ i : Class μ H G, MeasurableSet i.val)
    (τ : Class μ H G → Class μ H G) (hinv : Function.Involutive τ)
    (ht : ∀ i, (fun z => H (representative μ H G i,z)) =ᵐ[μ]
      (fun z => 1-H (representative μ H G (τ i),z)))
    (hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0<L (x,y) →
      (fun z => H (x,z)) =ᵐ[μ] (fun z => 1-H (y,z))) :
    ∀ i, μ.real i.val=μ.real (τ i).val := by
  have hf := transport_confined_to_partner μ H L G hL hG hm τ ht hc
  intro i
  apply TwoPairPartnerMass.partner_mass μ L hL bL sL d hd hr
    i.val (τ i).val (hm i) (hm (τ i)) (hf i)
  simpa only [hinv i] using hf (τ i)

lemma positive_transport_rectangle_value (μ : Measure Ω) [SFinite μ]
    (H L : Ω × Ω → ℝ) (X Y : Set Ω)
    (hY : MeasurableSet Y) (hpX : 0<μ X) (b : Bool)
    (hrect : H =ᵐ[(μ.restrict X).prod (μ.restrict Y)]
      (fun _ => if b then (1:ℝ) else 0))
    (hr : ∀ᵐ x ∂μ, 0<∫ y,L (x,y) ∂μ)
    (hf : ∀ᵐ p ∂μ.prod μ, p.1∈X → 0<L p → p.2∈Y)
    (hs : ∀ᵐ p ∂μ.prod μ, 0<L p → H p=1)
    (hX : MeasurableSet X) : b=true := by
  cases hb : b
  case true => rfl
  case false =>
    have hn : μ.restrict X ≠ 0 := by
      intro hz
      have hz' : μ X=0 := by
        simpa using congrArg (fun m : Measure Ω => m Set.univ) hz
      exact (ne_of_gt hpX) hz'
    letI : NeZero (μ.restrict X) := ⟨hn⟩
    have hrect' := Measure.ae_ae_of_ae_prod hrect
    obtain ⟨x,hx,hxr,hxf,hxs,hxrect⟩ :=
      ((ae_restrict_mem hX).and ((ae_restrict_of_ae hr).and
        ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hf)).and
          ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hs)).and hrect')))).exists
    have hzrow : ∀ᵐ y ∂μ, L (x,y)≤0 := by
      have hxy := (ae_restrict_iff' hY).mp hxrect
      filter_upwards [hxf,hxs,hxy] with y hyf hys hyr
      by_contra hnpos
      have hl := lt_of_not_ge hnpos
      have hv := hyr (hyf hx hl)
      have hv' := hys hl
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hv
      linarith
    exact False.elim ((not_lt_of_ge (integral_nonpos_of_ae hzrow)) hxr)

/-- Quotient extraction uses precisely the conull positive twin partition.
Regularity is only almost everywhere; representatives are not silently upgraded. -/
theorem extract_antipodal_quotient (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H L : Ω × Ω → ℝ) (hH : Measurable H) (hL : Measurable L)
    (bH : ∀ p, H p=0 ∨ H p=1) (sH : ∀ x y,H (x,y)=H (y,x))
    (bL : ∀ᵐ p ∂μ.prod μ,0≤L p ∧ L p≤1)
    (sL : ∀ᵐ p ∂μ.prod μ,L p=L (p.2,p.1))
    (d : ℝ) (hd : 0<d) (hr : ∀ᵐ x ∂μ,∫ y,L (x,y) ∂μ=d)
    (hLH : ∀ᵐ p ∂μ.prod μ,0<L p → H p=1)
    (hcomp : ∀ᵐ x ∂μ,∀ᵐ y ∂μ,0<L (x,y) →
      (fun z => H (x,z)) =ᵐ[μ] (fun z => 1-H (y,z)))
    (G : Set Ω) (hG : ∀ᵐ x ∂μ,x∈G)
    (hclasses : ∀ i : Class μ H G,MeasurableSet i.val ∧ 0<μ i.val)
    [Fintype (Class μ H G)] :
    ∃ (B : Class μ H G → Class μ H G → Bool) (τ : Class μ H G → Class μ H G),
      (∀ i j,B i j=B j i) ∧ Function.Injective (fun i => B i) ∧
      Function.Involutive τ ∧ (∀ i,τ i≠i) ∧
      (∀ i j,B (τ i) j= !(B i j)) ∧ (∀ i,B i i=false) ∧
      (∀ i,μ.real i.val=μ.real (τ i).val) ∧
      (∀ i j,H =ᵐ[(μ.restrict i.val).prod (μ.restrict j.val)]
        (fun _ => if B i j then (1:ℝ) else 0)) := by
  classical
  obtain ⟨x,hx⟩ := hG.exists
  letI : Nonempty (Class μ H G) :=
    ⟨⟨FourColorClasses.classSet G (Twin μ H) x,x,hx,rfl⟩⟩
  obtain ⟨B,hB⟩ := exists_block_table μ H hH bH sH G hclasses
  have hbr := fun i j => (hB i j).2.1
  have hbc := fun i j => (hB i j).2.2
  have hbs := block_table_symmetric μ H G B (fun i => (hclasses i).2) hbr hbc
  have hbi := block_table_injective μ H G hG (fun i => (hclasses i).1) B hbr
  have hpos : ∀ᵐ x ∂μ,0<∫ y,L (x,y) ∂μ := hr.mono (fun x hx => hx ▸ hd)
  have hex := exists_complementary_class μ H L G hG
    (fun i => (hclasses i).1) (fun i => (hclasses i).2) hpos hcomp
  choose τ ht using hex
  have htc := fun i => complementary_table_rows μ H G B
    (fun i => (hclasses i).2) hbr i (τ i) (ht i)
  obtain ⟨hinv,hnfix⟩ := partner_involution B hbi τ htc
  have hf := transport_confined_to_partner μ H L G hL hG
    (fun i => (hclasses i).1) τ ht hcomp
  have hdiag : ∀ i,B i i=false := by
    intro i
    have hp := positive_transport_rectangle_value μ H L i.val (τ i).val
      (hclasses (τ i)).1 (hclasses i).2 (B i (τ i)) (hB i (τ i)).1
      hpos (hf i) hLH (hclasses i).1
    have he := htc i i
    rw [hbs (τ i) i,hp] at he
    cases hh : B i i
    · rfl
    · simp only [hh, Bool.not_true] at he
      cases he
  exact ⟨B,τ,hbs,hbi,hinv,hnfix,htc,hdiag,
    equal_partner_masses μ H L G hL bL sL d hd hr hG
      (fun i => (hclasses i).1) τ hinv ht hcomp,
    fun i j => (hB i j).1⟩

lemma ae_ae_of_class_rectangles (μ : Measure Ω) [SFinite μ]
    (H : Ω × Ω → ℝ) (G : Set Ω) [Fintype (Class μ H G)]
    (hG : ∀ᵐ x ∂μ,x∈G) (hm : ∀ i : Class μ H G,MeasurableSet i.val)
    (P : Ω → Ω → Prop)
    (hP : ∀ i j : Class μ H G,
      ∀ᵐ x ∂μ.restrict i.val,∀ᵐ y ∂μ.restrict j.val,P x y) :
    ∀ᵐ x ∂μ,∀ᵐ y ∂μ,P x y := by
  apply ae_of_classes μ H G hG hm
  intro i
  have hh : ∀ᵐ x ∂μ.restrict i.val,∀ j : Class μ H G,
      ∀ᵐ y ∂μ.restrict j.val,P x y := ae_all_iff.mpr (hP i)
  filter_upwards [hh] with x hx
  exact ae_of_classes μ H G hG hm (P x) hx

end TwoPairSupportClassification
end


-- Local module: TwoPairSupportReconstruction
section
open MeasureTheory
open scoped BigOperators
open scoped Classical
namespace TwoPairSupportReconstruction
open TwoPairSupportClassification
variable {Ω : Type*} [MeasurableSpace Ω]

lemma class_member_eq (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω)
    (i j : Class μ H G) {x : Ω} (hi : x∈i.val) (hj : x∈j.val) : i=j :=
  class_eq_of_profiles μ H G i j ((member_row μ H G i hi).trans
    (member_row μ H G j hj).symm)

lemma class_cover (μ : Measure Ω) (H : Ω × Ω → ℝ) (G : Set Ω) :
    (⋃ i : Class μ H G, i.val)=G := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    rw [class_eq μ H G i] at hi
    exact hi.1
  · intro hx
    exact Set.mem_iUnion.mpr
      ⟨⟨FourColorClasses.classSet G (Twin μ H) x,x,hx,rfl⟩,hx,Filter.EventuallyEq.rfl⟩

lemma class_mass_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω × Ω → ℝ) (G : Set Ω) [Fintype (Class μ H G)]
    (hG : ∀ᵐ x ∂μ,x∈G) (hm : ∀ i : Class μ H G,MeasurableSet i.val) :
    ∑ i : Class μ H G, μ.real i.val=1 := by
  have hd : Pairwise (fun i j : Class μ H G => Disjoint i.val j.val) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj => hij (class_member_eq μ H G i j hi hj))
  rw [← measureReal_iUnion_fintype hd hm,class_cover μ H G]
  have he : G =ᵐ[μ] Set.univ := hG.mono (fun x hx =>
    propext (iff_of_true hx (Set.mem_univ x)))
  rw [measureReal_congr he]
  simp

lemma six_class_masses (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω × Ω → ℝ) (G : Set Ω) [Fintype (Class μ H G)]
    (hG : ∀ᵐ x ∂μ,x∈G) (hm : ∀ i : Class μ H G,MeasurableSet i.val)
    (hp : ∀ i : Class μ H G,(1/6:ℝ)≤μ.real i.val)
    (hn : Fintype.card (Class μ H G)=6) :
    ∀ i : Class μ H G,μ.real i.val=(1/6:ℝ) := by
  intro i
  apply le_antisymm _ (hp i)
  by_contra hh
  have hlt := Finset.sum_lt_sum (s := (Finset.univ : Finset (Class μ H G)))
    (fun j _ => hp j) ⟨i,Finset.mem_univ i,lt_of_not_ge hh⟩
  rw [class_mass_sum μ H G hG hm] at hlt
  norm_num [hn] at hlt

lemma two_cover {I : Type*} [Fintype I] [DecidableEq I]
    (hn : Fintype.card I=2) (a b : I) (hab : a≠b) : ∀ i,i=a ∨ i=b := by
  have he : ({a,b} : Finset I)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hn,hab]
  intro i
  have hi : i∈({a,b} : Finset I) := by rw [he]; exact Finset.mem_univ i
  simpa using hi

lemma two_class_half (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω × Ω → ℝ) (G : Set Ω) [Fintype (Class μ H G)]
    (hG : ∀ᵐ x ∂μ,x∈G) (hm : ∀ i : Class μ H G,MeasurableSet i.val)
    (hn : Fintype.card (Class μ H G)=2)
    (τ : Class μ H G → Class μ H G) (hnf : ∀ i,τ i≠i)
    (he : ∀ i,μ.real i.val=μ.real (τ i).val) :
    ∀ i : Class μ H G,μ.real i.val=(1/2:ℝ) := by
  classical
  intro i
  have hset : ({i,τ i} : Finset (Class μ H G))=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hn,Ne.symm (hnf i)]
  have hs := class_mass_sum μ H G hG hm
  rw [← hset] at hs
  simp only [Finset.sum_insert, Finset.mem_singleton, Ne.symm (hnf i), not_false_eq_true,
    Finset.sum_singleton] at hs
  linarith [he i]

noncomputable def cross (S : Set Ω) (p : Ω × Ω) : ℝ :=
  if p.1∈S then (if p.2∈S then 0 else 1) else (if p.2∈S then 1 else 0)

lemma measurable_cross (S : Set Ω) (hS : MeasurableSet S) : Measurable (cross S) := by
  classical
  exact Measurable.ite (hS.preimage measurable_fst)
    (Measurable.ite (hS.preimage measurable_snd) measurable_const measurable_const)
    (Measurable.ite (hS.preimage measurable_snd) measurable_const measurable_const)

lemma two_class_cut (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω × Ω → ℝ) (hH : Measurable H) (G : Set Ω)
    [Fintype (Class μ H G)] [Nonempty (Class μ H G)]
    (hG : ∀ᵐ x ∂μ,x∈G) (hm : ∀ i : Class μ H G,MeasurableSet i.val)
    (hn : Fintype.card (Class μ H G)=2)
    (B : Class μ H G → Class μ H G → Bool)
    (τ : Class μ H G → Class μ H G) (hnf : ∀ i,τ i≠i)
    (he : ∀ i,μ.real i.val=μ.real (τ i).val)
    (hs : ∀ i j,B i j=B j i) (hd : ∀ i,B i i=false)
    (hc : ∀ i j,B (τ i) j= !(B i j))
    (hr : ∀ i j,H =ᵐ[(μ.restrict i.val).prod (μ.restrict j.val)]
      (fun _ => if B i j then (1:ℝ) else 0)) :
    ∃ S : Set Ω,MeasurableSet S ∧ μ.real S=(1/2:ℝ) ∧ H =ᵐ[μ.prod μ] cross S := by
  classical
  obtain ⟨i⟩ := ‹Nonempty (Class μ H G)›
  refine ⟨i.val,hm i,two_class_half μ H G hG hm hn τ hnf he i,?_⟩
  have hcover := two_cover hn i (τ i) (Ne.symm (hnf i))
  have hcross : B i (τ i)=true := by rw [hs,hc,hd]; rfl
  have hval : ∀ j k,
      (if B j k then (1:ℝ) else 0)=
      (if j=i then (if k=i then 0 else 1) else (if k=i then 1 else 0)) := by
    intro j k
    have hrev : B (τ i) i=true := (hs (τ i) i).trans hcross
    rcases hcover j with hj | hj <;> rcases hcover k with hk | hk <;>
      rw [hj,hk] <;>
      simp only [hd,hcross,hrev,hnf i,Bool.false_eq_true,↓reduceIte]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hH (measurable_cross _ (hm i)))).mpr
  apply ae_ae_of_class_rectangles μ H G hG hm
  intro j k
  filter_upwards [ae_restrict_mem (hm j),Measure.ae_ae_of_ae_prod (hr j k)] with x hx hxr
  filter_upwards [ae_restrict_mem (hm k),hxr] with y hy hxy
  have hxiff : x∈i.val ↔ j=i := by
    constructor
    · exact fun h => class_member_eq μ H G j i hx h
    · intro h; simpa only [h] using hx
  have hyiff : y∈i.val ↔ k=i := by
    constructor
    · exact fun h => class_member_eq μ H G k i hy h
    · intro h; simpa only [h] using hy
  rw [cross,hxiff,hyiff]
  have hv := hval j k
  by_cases hji : j=i <;> by_cases hki : k=i <;>
    simp only [hji,hki,↓reduceIte] at hv hxy ⊢ <;> exact hxy.trans hv

lemma six_prism_blocks (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω × Ω → ℝ) (G : Set Ω)
    [Fintype (Class μ H G)] [Nonempty (Class μ H G)]
    (hG : ∀ᵐ x ∂μ,x∈G) (hm : ∀ i : Class μ H G,MeasurableSet i.val)
    (hp : ∀ i : Class μ H G,(1/6:ℝ)≤μ.real i.val)
    (hn : Fintype.card (Class μ H G)=6)
    (B : Class μ H G → Class μ H G → Bool)
    (τ : Class μ H G → Class μ H G)
    (hi : Function.Injective (fun i => B i)) (ht : Function.Involutive τ)
    (hs : ∀ i j,B i j=B j i) (hd : ∀ i,B i i=false)
    (hc : ∀ i j,B (τ i) j= !(B i j))
    (hr : ∀ i j,H =ᵐ[(μ.restrict i.val).prod (μ.restrict j.val)]
      (fun _ => if B i j then (1:ℝ) else 0)) :
    ∃ X : TwoPairAntipodal.Vertex → Set Ω,
      (∀ u,MeasurableSet (X u) ∧ μ.real (X u)=(1/6:ℝ)) ∧
      Pairwise (fun u v => Disjoint (X u) (X v)) ∧ (⋃ u,X u)=G ∧
      (∀ u v,H =ᵐ[(μ.restrict (X u)).prod (μ.restrict (X v))]
        (fun _ => if TwoPairAntipodal.prism u v then (1:ℝ) else 0)) := by
  classical
  obtain ⟨e,he⟩ := TwoPairAntipodalClassification.classify_six B τ ht hs hd hc hn
  have hpr : ∀ u v,B (e u) (e v)=true ↔ TwoPairAntipodal.prism u v := by
    rcases he with hb | hp
    · have heq : B (e (0,0))=B (e (1,0)) := by
        funext j
        obtain ⟨v,rfl⟩ := e.surjective j
        apply Bool.eq_iff_iff.mpr
        exact (hb (0,0) v).trans (hb (1,0) v).symm
      have heq' := e.injective (hi heq)
      have hbad := congrArg (fun v : TwoPairAntipodal.Vertex => v.1) heq'
      norm_num at hbad
    · exact hp
  refine ⟨fun u => (e u).val,?_,?_,?_,?_⟩
  · intro u
    exact ⟨hm (e u),six_class_masses μ H G hG hm hp hn (e u)⟩
  · intro u v huv
    apply Set.disjoint_left.mpr
    intro x hxu hxv
    exact huv (e.injective (class_member_eq μ H G (e u) (e v) hxu hxv))
  · calc
      (⋃ u,(e u).val) = ⋃ i : Class μ H G,i.val := by
        ext x
        constructor
        · intro hx
          obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨e u,hu⟩
        · intro hx
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
          obtain ⟨u,rfl⟩ := e.surjective i
          exact Set.mem_iUnion.mpr ⟨u,hi⟩
      _ = G := class_cover μ H G
  · intro u v
    simpa only [hpr u v] using hr (e u) (e v)

/-- Actual measurable support classification from the already-derived finite
positive twin-class interface. No block constancy or partner map is assumed. -/
theorem support_classification (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H L : Ω × Ω → ℝ) (hH : Measurable H) (hL : Measurable L)
    (bH : ∀ p,H p=0 ∨ H p=1) (sH : ∀ x y,H (x,y)=H (y,x))
    (bL : ∀ᵐ p ∂μ.prod μ,0≤L p ∧ L p≤1)
    (sL : ∀ᵐ p ∂μ.prod μ,L p=L (p.2,p.1))
    (d : ℝ) (hd : 0<d) (hr : ∀ᵐ x ∂μ,∫ y,L (x,y) ∂μ=d)
    (hLH : ∀ᵐ p ∂μ.prod μ,0<L p → H p=1)
    (hcomp : ∀ᵐ x ∂μ,∀ᵐ y ∂μ,0<L (x,y) →
      (fun z => H (x,z)) =ᵐ[μ] (fun z => 1-H (y,z)))
    (G : Set Ω) (hG : ∀ᵐ x ∂μ,x∈G)
    (hclasses : ∀ i : Class μ H G,MeasurableSet i.val ∧ (1/6:ℝ)≤μ.real i.val)
    (hfinite : (FourColorClasses.classFamily G (Twin μ H)).Finite)
    (hsize : (FourColorClasses.classFamily G (Twin μ H)).ncard≤6) :
    (∃ S : Set Ω,MeasurableSet S ∧ μ.real S=(1/2:ℝ) ∧ H =ᵐ[μ.prod μ] cross S) ∨
    (∃ X : TwoPairAntipodal.Vertex → Set Ω,
      (∀ u,MeasurableSet (X u) ∧ μ.real (X u)=(1/6:ℝ)) ∧
      Pairwise (fun u v => Disjoint (X u) (X v)) ∧ (⋃ u,X u)=G ∧
      (∀ u v,H =ᵐ[(μ.restrict (X u)).prod (μ.restrict (X v))]
        (fun _ => if TwoPairAntipodal.prism u v then (1:ℝ) else 0))) := by
  classical
  letI : Fintype (Class μ H G) := hfinite.fintype
  obtain ⟨x,hx⟩ := hG.exists
  letI : Nonempty (Class μ H G) :=
    ⟨⟨FourColorClasses.classSet G (Twin μ H) x,x,hx,rfl⟩⟩
  have hp : ∀ i : Class μ H G,0<μ i.val := by
    intro i
    have hh : 0<μ.real i.val := lt_of_lt_of_le (by norm_num) (hclasses i).2
    exact (ENNReal.toReal_pos_iff.mp hh).1
  obtain ⟨B,τ,hbs,hbi,hti,htn,htc,hbd,hpm,hrect⟩ :=
    extract_antipodal_quotient μ H L hH hL bH sH bL sL d hd hr hLH hcomp G hG
      (fun i => ⟨(hclasses i).1,hp i⟩)
  have hn : Fintype.card (Class μ H G)≤6 := by
    simpa only [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card] using hsize
  have hcard := TwoPairAntipodalQuotient.card_two_or_six B τ hn hti htn hbs hbd htc hbi
  rcases hcard with htwo | hsix
  · exact Or.inl (two_class_cut μ H hH G hG (fun i => (hclasses i).1) htwo
      B τ htn hpm hbs hbd htc hrect)
  · exact Or.inr (six_prism_blocks μ H G hG (fun i => (hclasses i).1)
      (fun i => (hclasses i).2) hsix B τ hbi hti hbs hbd htc hrect)

end TwoPairSupportReconstruction

end


-- Local module: TwoPairStructuralReduction
section
open MeasureTheory
open scoped Classical
namespace TwoPairStructuralReduction
open FourColorKernels TwoPairCycleReduction TwoPairFiniteReduction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma sum_rows (A B : Ω × Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p,0≤ A p ∧ A p≤1) (bB : ∀ p,0≤ B p ∧ B p≤1)
    (a b : ℝ) (ra : ∀ᵐ x ∂μ,∫ y,A (x,y) ∂μ=a)
    (rb : ∀ᵐ x ∂μ,∫ y,B (x,y) ∂μ=b) :
    ∀ᵐ x ∂μ,∫ y,(A (x,y)+B (x,y)) ∂μ=a+b := by
  filter_upwards [ra,rb] with x hx hy
  have hiA : Integrable (fun y => A (x,y)) μ :=
    unit_integrable μ _ (hA.comp (measurable_const.prodMk measurable_id)) (fun y => bA (x,y))
  have hiB : Integrable (fun y => B (x,y)) μ :=
    unit_integrable μ _ (hB.comp (measurable_const.prodMk measurable_id)) (fun y => bB (x,y))
  calc
    _ = (∫ y,A (x,y) ∂μ)+(∫ y,B (x,y) ∂μ) := integral_add hiA hiB
    _ = a+b := by rw [hx,hy]


lemma mixed_bounds (A B : Ω × Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p,0≤ A p ∧ A p≤1) (bB : ∀ p,0≤ B p ∧ B p≤1)
    (bQ : ∀ p,0≤ A p+B p ∧ A p+B p≤1) :
    ∀ p,0≤ comp μ A B p+comp μ B A p ∧ comp μ A B p+comp μ B A p≤1 := by
  intro p
  refine ⟨add_nonneg (comp_bounds μ A B hA hB bA bB p).1
    (comp_bounds μ B A hB hA bB bA p).1,?_⟩
  exact (TwoPairHalfSupportBridge.remainder_square_dom μ A B (fun p => A p+B p)
    hA hB (hA.add hB) bA bB bQ (fun _ => rfl) p).trans
    (comp_bounds μ _ _ (hA.add hB) (hA.add hB) bQ bQ p).2

lemma mixed_symmetry (A B : Ω × Ω → ℝ)
    (sA : ∀ x y,A (x,y)=A (y,x)) (sB : ∀ x y,B (x,y)=B (y,x)) (x y : Ω) :
    comp μ A B (x,y)+comp μ B A (x,y)=comp μ A B (y,x)+comp μ B A (y,x) := by
  rw [comp_swap μ A B sA sB x y,comp_swap μ B A sB sA x y]
  ring

lemma reduced_word (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i,Measurable (W i)) (hb : ∀ i p,0≤ W i p ∧ W i p≤1)
    (hs : ∀ i x y,W i (x,y)=W i (y,x))
    (hr : ∀ i,∀ᵐ x ∂μ,∫ y,W i (x,y) ∂μ=(1/6:ℝ))
    (hz : ∀ σ : Equiv.Perm (Fin 6),LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (TwoPairWords.color (σ i)))=0)
    (f : Fin 6 → Fin 6) (hf : Function.Bijective f)
    (he : TwoPairWords.color (f 1)=TwoPairWords.color (f 0)) :
    closing4 μ (W (TwoPairWords.color (f 2))) (W (TwoPairWords.color (f 3)))
      (W (TwoPairWords.color (f 4))) (W (TwoPairWords.color (f 5)))=0 := by
  exact remove_repeated_prefix μ (fun i => W (TwoPairWords.color (f i)))
    (fun i => hm _) (fun i p => hb _ p) (congrArg W he) (hs _)
    (1/6) (by norm_num) (hr _) (TwoPairWords.zero_of_permutation μ W hz f hf)

lemma reduced_words (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i,Measurable (W i)) (hb : ∀ i p,0≤ W i p ∧ W i p≤1)
    (hs : ∀ i x y,W i (x,y)=W i (y,x))
    (hr : ∀ i,∀ᵐ x ∂μ,∫ y,W i (x,y) ∂μ=(1/6:ℝ))
    (hz : ∀ σ : Equiv.Perm (Fin 6),LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (TwoPairWords.color (σ i)))=0) :
    closing4 μ (W 0) (W 0) (W 2) (W 3)=0 ∧
    closing4 μ (W 0) (W 2) (W 0) (W 3)=0 ∧
    closing4 μ (W 1) (W 1) (W 2) (W 3)=0 ∧
    closing4 μ (W 1) (W 2) (W 1) (W 3)=0 := by
  exact ⟨reduced_word μ W hm hb hs hr hz ![2,3,0,1,4,5] (by decide) (by rfl),
    reduced_word μ W hm hb hs hr hz ![2,3,0,4,1,5] (by decide) (by rfl),
    reduced_word μ W hm hb hs hr hz ![0,1,2,3,4,5] (by decide) (by rfl),
    reduced_word μ W hm hb hs hr hz ![0,1,2,4,3,5] (by decide) (by rfl)⟩

lemma binary_half_pair (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ x,f x=0 ∨ f x=1) (bg : ∀ x,g x=0 ∨ g x=1)
    (rf : ∫ x,f x ∂μ=(1/2:ℝ)) (rg : ∫ x,g x ∂μ=(1/2:ℝ))
    (hd : ∀ᵐ x ∂μ,¬(f x=1 ∧ g x=1)) :
    f =ᵐ[μ] (fun x => 1-g x) := by
  have uf : ∀ x,0≤ f x ∧ f x≤1 := by intro x; rcases bf x with h | h <;> simp [h]
  have ug : ∀ x,0≤ g x ∧ g x≤1 := by intro x; rcases bg x with h | h <;> simp [h]
  have hfi := unit_integrable μ f hf uf
  have hgi := unit_integrable μ g hg ug
  have hn : ∀ᵐ x ∂μ,0≤1-f x-g x := by
    filter_upwards [hd] with x hx
    rcases bf x with hf | hf <;> rcases bg x with hg | hg <;> simp [hf,hg] at hx ⊢
  have hz : (∫ x,1-f x-g x ∂μ)=0 := by
    calc
      _ = (∫ x,1-f x ∂μ)-(∫ x,g x ∂μ) :=
        integral_sub ((integrable_const (1:ℝ)).sub hfi) hgi
      _ = (∫ _x : Ω,(1:ℝ) ∂μ)-(∫ x,f x ∂μ)-(∫ x,g x ∂μ) := by
        congr 1
        exact integral_sub (integrable_const (1:ℝ)) hfi
      _ = 0 := by rw [rf,rg]; norm_num

  have he := (integral_eq_zero_iff_of_nonneg_ae hn (((integrable_const (1:ℝ)).sub hfi).sub hgi)).mp hz
  filter_upwards [he] with x hx
  change 1-f x-g x=0 at hx
  linarith

lemma support_half_row (P : Ω × Ω → ℝ) (hP : Measurable P) (x : Ω)
    (hx : μ {y | 0< P (x,y)}=(1:ENNReal)/2) :
    (∫ y,supportKernel P (x,y) ∂μ)=(1/2:ℝ) := by
  have hs : MeasurableSet {y | 0< P (x,y)} :=
    measurableSet_lt measurable_const (hP.comp (measurable_const.prodMk measurable_id))
  have he : (fun y => supportKernel P (x,y))=
      Set.indicator {y | 0< P (x,y)} (fun _ => (1:ℝ)) := by
    funext y
    rfl
  rw [he,integral_indicator_const _ hs]
  simp only [measureReal_def,hx]
  norm_num

lemma complementary_support_rows (P L : Ω × Ω → ℝ) (hP : Measurable P) (hL : Measurable L)
    (bP : ∀ p,0≤ P p ∧ P p≤1) (sP : ∀ x y,P (x,y)=P (y,x))
    (hz : ∀ᵐ p ∂μ.prod μ,comp μ P P p*L p=0)
    (hh : ∀ᵐ x ∂μ,μ {y | 0< P (x,y)}=(1:ENNReal)/2) :
    ∀ᵐ x ∂μ,∀ᵐ y ∂μ,0< L (x,y) →
      (fun z => supportKernel P (x,z)) =ᵐ[μ] (fun z => 1-supportKernel P (y,z)) := by
  have hd := (TwoPairHalfSupportBridge.independence_and_disjointness μ P L hP hL bP sP hz).2
  filter_upwards [hh,hd] with x hx hxd
  filter_upwards [hh,hxd] with y hy hyd
  intro hxy
  apply binary_half_pair μ _ _
    ((supportKernel_measurable P hP).comp (measurable_const.prodMk measurable_id))
    ((supportKernel_measurable P hP).comp (measurable_const.prodMk measurable_id))
    (fun z => supportKernel_binary P (x,z)) (fun z => supportKernel_binary P (y,z))
    (support_half_row μ P hP x hx) (support_half_row μ P hP y hy)
  filter_upwards [hyd hxy] with z hz
  intro hp
  have hxz : 0< P (x,z) := by
    by_contra hn
    simp [supportKernel,hn] at hp
  have hyz : 0< P (y,z) := by
    by_contra hn
    simp [supportKernel,hn] at hp
  exact hz ⟨hxz,hyz⟩

noncomputable def mixed (W : Fin 4 → Ω × Ω → ℝ) : Ω × Ω → ℝ :=
  fun p => comp μ (W 0) (W 1) p+comp μ (W 1) (W 0) p

noncomputable def singletonMixed (W : Fin 4 → Ω × Ω → ℝ) : Ω × Ω → ℝ :=
  fun p => comp μ (W 2) (W 3) p+comp μ (W 3) (W 2) p

def remainder (W : Fin 4 → Ω × Ω → ℝ) : Ω × Ω → ℝ := fun p => W 2 p+W 3 p

structure NormalizedFacts (W : Fin 4 → Ω × Ω → ℝ) : Prop where
  q_cap : ∀ p,0≤ W 0 p+W 1 p ∧ W 0 p+W 1 p≤1/2
  r_cap : ∀ p,0≤ remainder W p ∧ remainder W p≤1
  p_cap : ∀ p,0≤ mixed μ W p ∧ mixed μ W p≤1
  l_cap : ∀ p,0≤ singletonMixed μ W p ∧ singletonMixed μ W p≤1
  q_row : ∀ᵐ x ∂μ,∫ y,(W 0 (x,y)+W 1 (x,y)) ∂μ=(1/3:ℝ)
  r_row : ∀ᵐ x ∂μ,∫ y,remainder W (x,y) ∂μ=(1/3:ℝ)
  l_row : ∀ᵐ x ∂μ,∫ y,singletonMixed μ W (x,y) ∂μ=(1/18:ℝ)
  p_row : ∀ᵐ x ∂μ,∫ y,mixed μ W (x,y) ∂μ=(1/18:ℝ)
  q_square : ∀ᵐ p ∂μ.prod μ,
    comp μ (fun p => W 0 p+W 1 p) (fun p => W 0 p+W 1 p) p=
      (1/12:ℝ)+comp μ (remainder W) (remainder W) p/4
  zero_a : ∀ᵐ p ∂μ.prod μ,comp μ (W 0) (W 0) p*singletonMixed μ W p=0
  zero_b : ∀ᵐ p ∂μ.prod μ,comp μ (W 1) (W 1) p*singletonMixed μ W p=0
  zero_p : ∀ᵐ p ∂μ.prod μ,comp μ (mixed μ W) (mixed μ W) p*singletonMixed μ W p=0
  half : ∀ᵐ x ∂μ,μ {y | 0< mixed μ W (x,y)}=(1:ENNReal)/2
  adjacency : ∀ᵐ p ∂μ.prod μ,0< singletonMixed μ W p → supportKernel (mixed μ W) p=1
  complementary : ∀ᵐ x ∂μ,∀ᵐ y ∂μ,0< singletonMixed μ W (x,y) →
    (fun z => supportKernel (mixed μ W) (x,z)) =ᵐ[μ]
      (fun z => 1-supportKernel (mixed μ W) (y,z))
  four_cycles : closing4 μ (W 0) (W 0) (W 2) (W 3)=0 ∧
    closing4 μ (W 0) (W 2) (W 0) (W 3)=0 ∧
    closing4 μ (W 1) (W 1) (W 2) (W 3)=0 ∧
    closing4 μ (W 1) (W 2) (W 1) (W 3)=0
  finite_classes : ∃ G : Set Ω,MeasurableSet G ∧ (∀ᵐ x ∂μ,x∈G) ∧
    let Rel := TwoPairSupportClassification.Twin μ (supportKernel (mixed μ W))
    (∀ x∈G,MeasurableSet (FourColorClasses.classSet G Rel x) ∧
      (1/6:ℝ)≤μ.real (FourColorClasses.classSet G Rel x)) ∧
    (FourColorClasses.classFamily G Rel).Finite ∧
    (FourColorClasses.classFamily G Rel).ncard≤6 ∧
    (FourColorClasses.classFamily G Rel).PairwiseDisjoint id ∧
    ⋃₀ FourColorClasses.classFamily G Rel=G

def Conclusion (H : Ω × Ω → ℝ) : Prop :=
  (∃ S : Set Ω,MeasurableSet S ∧ μ.real S=(1/2:ℝ) ∧
    H =ᵐ[μ.prod μ] TwoPairSupportReconstruction.cross S) ∨
  (∃ G : Set Ω,MeasurableSet G ∧ (∀ᵐ x ∂μ,x∈G) ∧
    ∃ X : TwoPairAntipodal.Vertex → Set Ω,
      (∀ u,MeasurableSet (X u) ∧ μ.real (X u)=(1/6:ℝ)) ∧
      Pairwise (fun u v => Disjoint (X u) (X v)) ∧ (⋃ u,X u)=G ∧
      (∀ u v,H =ᵐ[(μ.restrict (X u)).prod (μ.restrict (X v))]
        (fun _ => if TwoPairAntipodal.prism u v then (1:ℝ) else 0)))

theorem normalized_analytic_facts (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i,Measurable (W i)) (hb : ∀ i p,0≤ W i p ∧ W i p≤1)
    (hs : ∀ i x y,W i (x,y)=W i (y,x))
    (hr : ∀ i,∀ᵐ x ∂μ,∫ y,W i (x,y) ∂μ=(1/6:ℝ))
    (hpart : ∀ p,2*W 0 p+2*W 1 p+W 2 p+W 3 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6),LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (TwoPairWords.color (σ i)))=0) :
    NormalizedFacts μ W := by
  let A := W 0
  let B := W 1
  let C := W 2
  let D := W 3
  let Q := fun p => A p+B p
  let R := fun p => C p+D p
  let P := mixed μ W
  let L := fun p => comp μ C D p+comp μ D C p
  have hQ : Measurable Q := (hm 0).add (hm 1)
  have hR : Measurable R := (hm 2).add (hm 3)
  have bQhalf : ∀ p,0≤ Q p ∧ Q p≤1/2 := by
    intro p
    dsimp only [Q,A,B]
    constructor <;> linarith [(hb 0 p).1,(hb 1 p).1,(hb 2 p).1,(hb 3 p).1,hpart p]
  have bQ : ∀ p,0≤ Q p ∧ Q p≤1 := fun p => ⟨(bQhalf p).1,(bQhalf p).2.trans (by norm_num)⟩
  have bR : ∀ p,0≤ R p ∧ R p≤1 := by
    intro p
    dsimp only [R,C,D]
    constructor <;> linarith [(hb 0 p).1,(hb 1 p).1,(hb 2 p).1,(hb 3 p).1,hpart p]
  have sR : ∀ x y,R (x,y)=R (y,x) := by
    intro x y
    dsimp only [R,C,D]
    rw [hs 2 x y,hs 3 x y]
  have rQ : ∀ᵐ x ∂μ,∫ y,Q (x,y) ∂μ=(1/3:ℝ) := by
    simpa only [show (1/6:ℝ)+1/6=1/3 by norm_num] using
      sum_rows μ A B (hm 0) (hm 1) (hb 0) (hb 1) (1/6) (1/6) (hr 0) (hr 1)
  have rR : ∀ᵐ x ∂μ,∫ y,R (x,y) ∂μ=(1/3:ℝ) := by
    simpa only [show (1/6:ℝ)+1/6=1/3 by norm_num] using
      sum_rows μ C D (hm 2) (hm 3) (hb 2) (hb 3) (1/6) (1/6) (hr 2) (hr 3)
  have hP : Measurable P := (measurable_comp μ A B (hm 0) (hm 1)).add
    (measurable_comp μ B A (hm 1) (hm 0))
  have hL : Measurable L := (measurable_comp μ C D (hm 2) (hm 3)).add
    (measurable_comp μ D C (hm 3) (hm 2))
  have bP := mixed_bounds μ A B (hm 0) (hm 1) (hb 0) (hb 1) bQ
  have bL := mixed_bounds μ C D (hm 2) (hm 3) (hb 2) (hb 3) bR
  have sP := mixed_symmetry μ A B (hs 0) (hs 1)
  have sL := mixed_symmetry μ C D (hs 2) (hs 3)
  have rL : ∀ᵐ x ∂μ,∫ y,L (x,y) ∂μ=(1/18:ℝ) := by
    have rCD := comp_row μ C D (hm 2) (hm 3) (hb 2) (hb 3) (1/6) (1/6) (hr 2) (hr 3)
    have rDC := comp_row μ D C (hm 3) (hm 2) (hb 3) (hb 2) (1/6) (1/6) (hr 3) (hr 2)
    simpa only [show (1/6:ℝ)*(1/6)+(1/6)*(1/6)=1/18 by norm_num] using
      sum_rows μ (comp μ C D) (comp μ D C)
        (measurable_comp μ C D (hm 2) (hm 3)) (measurable_comp μ D C (hm 3) (hm 2))
        (comp_bounds μ C D (hm 2) (hm 3) (hb 2) (hb 3))
        (comp_bounds μ D C (hm 3) (hm 2) (hb 3) (hb 2)) _ _ rCD rDC
  have rP : ∀ᵐ x ∂μ,∫ y,P (x,y) ∂μ=(1/18:ℝ) := by
    have rAB := comp_row μ A B (hm 0) (hm 1) (hb 0) (hb 1) (1/6) (1/6) (hr 0) (hr 1)
    have rBA := comp_row μ B A (hm 1) (hm 0) (hb 1) (hb 0) (1/6) (1/6) (hr 1) (hr 0)
    simpa only [P,mixed,A,B,show (1/6:ℝ)*(1/6)+(1/6)*(1/6)=1/18 by norm_num] using
      sum_rows μ (comp μ A B) (comp μ B A)
        (measurable_comp μ A B (hm 0) (hm 1)) (measurable_comp μ B A (hm 1) (hm 0))
        (comp_bounds μ A B (hm 0) (hm 1) (hb 0) (hb 1))
        (comp_bounds μ B A (hm 1) (hm 0) (hb 1) (hb 0)) _ _ rAB rBA
  have eqQ : Q=(fun p => (1-R p)/2) := by
    funext p
    dsimp only [Q,R,A,B,C,D]
    linarith [hpart p]
  have eQ : ∀ᵐ p ∂μ.prod μ,comp μ Q Q p=(1/12:ℝ)+comp μ R R p/4 := by
    rw [eqQ]
    exact TwoPairKernelIdentities.complement_square_ae μ R hR bR sR rR
  obtain ⟨zAACD,zACAD,zBBCD,zBCBD⟩ := reduced_words μ W hm hb hs hr hz
  have zA := TwoPairFourCycleProducts.repeated_product_zero μ A C D
    (hm 0) (hm 2) (hm 3) (hb 0) (hb 2) (hb 3) (hs 0) (hs 2) (hs 3) zAACD
  have zB := TwoPairFourCycleProducts.repeated_product_zero μ B C D
    (hm 1) (hm 2) (hm 3) (hb 1) (hb 2) (hb 3) (hs 1) (hs 2) (hs 3) zBBCD
  have zP := TwoPairCompositionZeros.mixed_square_zero μ A B C D
    (hm 0) (hm 1) (hm 2) (hm 3) (hb 0) (hb 1) (hb 2) (hb 3)
    (hs 0) (hs 1) (hs 2) (hs 3) (TwoPairWords.mixed_words μ W hz)
  have eP : ∀ᵐ p ∂μ.prod μ,P p=comp μ A B p+comp μ B A p := Filter.Eventually.of_forall (fun _ => rfl)
  have dom : ∀ᵐ p ∂μ.prod μ,L p≤ comp μ R R p := Filter.Eventually.of_forall (fun p =>
    TwoPairHalfSupportBridge.remainder_square_dom μ C D R (hm 2) (hm 3) hR
      (hb 2) (hb 3) bR (fun _ => rfl) p)
  have hh := TwoPairHalfSupportBridge.half_support_from_compositions μ A B P L R
    (hm 0) (hm 1) hP hL (hb 0) (hb 1) bP bL (hs 0) (hs 1) sP sL
    (fun x z => bQhalf (x,z)) rQ (1/18) (by norm_num) rL eP eQ dom zA zB zP
  obtain ⟨G,hGm,hG,hcls,hfin,hn,hdis,hcover⟩ := finite_reduction μ A B C D P L R
    (hm 0) (hm 1) (hm 2) (hm 3) hP hL hR
    (hb 0) (hb 1) (hb 2) (hb 3) bP bL bR
    (hs 0) (hs 1) (hs 2) (hs 3) sP sL
    (fun x z => bQhalf (x,z)) rQ (hr 2) (hr 3) eP (fun _ => rfl) (fun _ => rfl)
    eQ zA zB zP
  have hLH : ∀ᵐ p ∂μ.prod μ,0< L p → supportKernel P p=1 := by
    filter_upwards [zA,zB,eQ] with p ha hb' hq
    intro hl
    have ha0 := (mul_eq_zero.mp ha).resolve_right (ne_of_gt hl)
    have hb0 := (mul_eq_zero.mp hb').resolve_right (ne_of_gt hl)
    have hexpand := TwoPairCompositionZeros.comp_four_add μ A B A B
      (hm 0) (hm 1) (hm 0) (hm 1) (hb 0) (hb 1) (hb 0) (hb 1) p
    have hpp : 0< P p := by
      dsimp only [P,mixed]
      change comp μ Q Q p = _ at hexpand
      have hnR := (comp_bounds μ R R hR hR bR bR p).1
      linarith
    simp [supportKernel,hpp]
  have hc := complementary_support_rows μ P L hP hL bP sP zP hh
  have hmH := supportKernel_measurable P hP
  have hsH := supportKernel_symm P sP
  exact ⟨bQhalf,bR,bP,bL,rQ,rR,rL,rP,eQ,zA,zB,zP,hh,hLH,hc,
    ⟨zAACD,zACAD,zBBCD,zBCBD⟩,⟨G,hGm,hG,hcls,hfin,hn,hdis,hcover⟩⟩

theorem normalized_structural_reduction (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i,Measurable (W i)) (hb : ∀ i p,0≤ W i p ∧ W i p≤1)
    (hs : ∀ i x y,W i (x,y)=W i (y,x))
    (hr : ∀ i,∀ᵐ x ∂μ,∫ y,W i (x,y) ∂μ=(1/6:ℝ))
    (hpart : ∀ p,2*W 0 p+2*W 1 p+W 2 p+W 3 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6),LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (TwoPairWords.color (σ i)))=0) :
    Conclusion μ (supportKernel (mixed μ W)) := by
  have facts := normalized_analytic_facts μ W hm hb hs hr hpart hz
  let P := mixed μ W
  let L := singletonMixed μ W
  have hP : Measurable P := (measurable_comp μ (W 0) (W 1) (hm 0) (hm 1)).add
    (measurable_comp μ (W 1) (W 0) (hm 1) (hm 0))
  have hL : Measurable L := (measurable_comp μ (W 2) (W 3) (hm 2) (hm 3)).add
    (measurable_comp μ (W 3) (W 2) (hm 3) (hm 2))
  have sP := mixed_symmetry μ (W 0) (W 1) (hs 0) (hs 1)
  have sL := mixed_symmetry μ (W 2) (W 3) (hs 2) (hs 3)
  have bL := facts.l_cap
  have rL := facts.l_row
  have hLH := facts.adjacency
  have hc := facts.complementary
  have hmH := supportKernel_measurable P hP
  have hsH := supportKernel_symm P sP
  obtain ⟨G,hGm,hG,hcls,hfin,hn,_,_⟩ := facts.finite_classes
  have hclasses : ∀ i : TwoPairSupportClassification.Class μ (supportKernel P) G,
      MeasurableSet i.val ∧ (1/6:ℝ)≤μ.real i.val := by
    intro i
    obtain ⟨x,hx,he⟩ := i.property
    rw [he]
    exact hcls x hx
  have hout := TwoPairSupportReconstruction.support_classification μ (supportKernel P) L hmH hL
    (supportKernel_binary P) hsH (Filter.Eventually.of_forall bL)
    (Filter.Eventually.of_forall (fun p => sL p.1 p.2)) (1/18) (by norm_num) rL hLH hc
    G hG hclasses hfin hn
  rcases hout with hcut | hprism
  · exact Or.inl hcut
  · exact Or.inr ⟨G,hGm,hG,hprism⟩

/-- Canonical a.e. hypotheses produce a pointwise normalized representative
and the actual mixed-support structural dichotomy, preserving every cycle. -/
theorem structural_reduction (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i,Measurable (W i))
    (hb : ∀ i,∀ᵐ p ∂μ.prod μ,0≤ W i p ∧ W i p≤1)
    (hs : ∀ i,∀ᵐ p ∂μ.prod μ,W i p=W i (p.2,p.1))
    (hr : ∀ i,∀ᵐ x ∂μ,∫ y,W i (x,y) ∂μ=(1/6:ℝ))
    (hp : ∀ᵐ p ∂μ.prod μ,2*W 0 p+2*W 1 p+W 2 p+W 3 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6),LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (TwoPairWords.color (σ i)))=0) :
    ∃ V : Fin 4 → Ω × Ω → ℝ,
      (∀ i,Measurable (V i)) ∧ (∀ i p,0≤ V i p ∧ V i p≤1) ∧
      (∀ i x y,V i (x,y)=V i (y,x)) ∧
      (∀ p,2*V 0 p+2*V 1 p+V 2 p+V 3 p=1) ∧
      (∀ i,V i =ᵐ[μ.prod μ] W i) ∧
      (∀ i,∀ᵐ x ∂μ,∫ y,V i (x,y) ∂μ=(1/6:ℝ)) ∧
      (∀ σ : Equiv.Perm (Fin 6),LowSupportCycle.cycleNested (μ := μ)
        (fun i => V (TwoPairWords.color (σ i)))=0) ∧
      Conclusion μ (supportKernel (mixed μ V)) := by
  obtain ⟨V,hVm,hVb,hVs,hVp,hVe,_,hVr,hVcycles⟩ :=
    TwoPairNormalization.normalize μ W hm hb hs hp
  have hrows : ∀ i,∀ᵐ x ∂μ,∫ y,V i (x,y) ∂μ=(1/6:ℝ) := by
    intro i
    filter_upwards [hVr i,hr i] with x hx hy
    exact hx.trans hy
  have hzero : ∀ σ : Equiv.Perm (Fin 6),LowSupportCycle.cycleNested (μ := μ)
      (fun i => V (TwoPairWords.color (σ i)))=0 := by
    intro σ
    exact (hVcycles (fun i => TwoPairWords.color (σ i))).trans (hz σ)
  have hsym : ∀ i x y,V i (x,y)=V i (y,x) := fun i x y => hVs i (x,y)
  exact ⟨V,hVm,hVb,hsym,hVp,hVe,hrows,hzero,
    normalized_structural_reduction μ V hVm hVb hsym hrows hVp hzero⟩

end TwoPairStructuralReduction


end


-- Local module: TwoPairDenseInvariant
section
open MeasureTheory
namespace TwoPairDenseInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A kernel of row degree greater than half its pointwise cap has no nontrivial
binary invariant cut. No symmetry or pointwise regularity is required. -/
theorem binary_invariant_constant
    (K : Ω × Ω → ℝ) (hK : Measurable K) (c k : ℝ)
    (bK : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p ∧ K p ≤ c)
    (rK : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ=k)
    (hgap : c < 2*k)
    (t : Ω → ℝ) (ht : Measurable t) (bt : ∀ᵐ x ∂μ, t x=0 ∨ t x=1)
    (hpres : ∀ᵐ p ∂μ.prod μ, 0 < K p → t p.1=t p.2) :
    (t =ᵐ[μ] (fun _ => 0)) ∨ (t =ᵐ[μ] (fun _ => 1)) := by
  have hit : Integrable t μ := by
    apply Integrable.of_bound ht.aestronglyMeasurable 1
    filter_upwards [bt] with x hx
    rcases hx with hx | hx <;> simp [hx]
  have hi1t : Integrable (fun x => 1-t x) μ := (integrable_const _).sub hit
  let m : ℝ := ∫ x, t x ∂μ
  have hbounds : ∀ᵐ x ∂μ,
      (t x=1 → k ≤ c*m) ∧ (t x=0 → k ≤ c*(1-m)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod bK,rK,Measure.ae_ae_of_ae_prod hpres] with x bx rx px
    have hiK : Integrable (fun y => K (x,y)) μ := by
      apply Integrable.of_bound (hK.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable c
      filter_upwards [bx] with y hy
      simpa [Real.norm_eq_abs,abs_of_nonneg hy.1] using hy.2
    constructor
    · intro tx
      have hle : ∀ᵐ y ∂μ, K (x,y) ≤ c*t y := by
        filter_upwards [bx,px,bt] with y byy pxy tyy
        rcases tyy with ty | ty
        · have hnp : ¬ 0 < K (x,y) := by
            intro hp
            have he := pxy hp
            rw [tx,ty] at he
            norm_num at he
          simpa [ty] using le_of_not_gt hnp
        · simpa [ty] using byy.2
      have hh := integral_mono_ae hiK (hit.const_mul c) hle
      rw [rx,integral_const_mul] at hh
      exact hh
    · intro tx
      have hle : ∀ᵐ y ∂μ, K (x,y) ≤ c*(1-t y) := by
        filter_upwards [bx,px,bt] with y byy pxy tyy
        rcases tyy with ty | ty
        · simpa [ty] using byy.2
        · have hnp : ¬ 0 < K (x,y) := by
            intro hp
            have he := pxy hp
            rw [tx,ty] at he
            norm_num at he
          simpa [ty] using le_of_not_gt hnp
      have hh := integral_mono_ae hiK (hi1t.const_mul c) hle
      rw [rx,integral_const_mul,integral_sub (integrable_const _) hit] at hh
      simpa [m] using hh
  by_cases hm : k ≤ c*m
  · right
    filter_upwards [hbounds,bt] with x hx htx
    rcases htx with htx | htx
    · have hh := hx.2 htx
      exfalso
      nlinarith
    · exact htx
  · left
    filter_upwards [hbounds,bt] with x hx htx
    rcases htx with htx | htx
    · exact htx
    · exact False.elim (hm (hx.1 htx))

end TwoPairDenseInvariant
end


-- Local module: TwoPairBipartiteOrientation
section
open MeasureTheory
namespace TwoPairBipartiteOrientation
open FourColorKernels FourColorTwinBlock TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma mixed_block_energy (X : Set Ω) (A B : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (sB : ∀ x y, B (x,y)=B (y,x)) :
    (∫ p, comp μ A B p ∂(μ.restrict X).prod (μ.restrict X)) =
      ∫ z, flux (μ.restrict X) A z * flux (μ.restrict X) B z ∂μ := by
  let ν := μ.restrict X
  have hm : Measurable (fun p : (Ω × Ω) × Ω => A (p.1.1,p.2)*B (p.2,p.1.2)) := by fun_prop
  have hi : Integrable (fun p : (Ω × Ω) × Ω => A (p.1.1,p.2)*B (p.2,p.1.2)) ((ν.prod ν).prod μ) :=
    unit_integrable _ _ hm (fun p => mul_unit (bA _) (bB _))
  unfold comp
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have he : (fun p : Ω × Ω => A (p.1,z)*B (z,p.2)) =
      fun p => A (p.1,z)*B (p.2,z) := by funext p; rw [sB z p.2]
  change (∫ p, A (p.1,z)*B (z,p.2) ∂ν.prod ν) = _
  rw [he]
  simpa [flux] using (integral_prod_mul (μ := ν) (ν := ν) (fun x => A (x,z)) (fun y => B (y,z)))

lemma opposite_orientation (a b d : ℝ) (hd : 0 < d)
    (ha : 0 ≤ a ∧ a ≤ d) (hb : 0 ≤ b ∧ b ≤ d)
    (h0 : a*b=0) (h1 : (d-a)*(d-b)=0) :
    (a=d ∧ b=0) ∨ (a=0 ∧ b=d) := by
  rcases mul_eq_zero.mp h0 with ha0 | hb0
  · right
    constructor
    · exact ha0
    · rw [ha0,sub_zero] at h1
      have h := (mul_eq_zero.mp h1).resolve_left (ne_of_gt hd)
      linarith
  · left
    constructor
    · rw [hb0,sub_zero] at h1
      have h := (mul_eq_zero.mp h1).resolve_right (ne_of_gt hd)
      linarith
    · exact hb0

/-- Symmetric opposing row orientations align with the original cut when the
sum kernel has degree greater than half its cap. -/
lemma orientation_alignment (Q : Ω × Ω → ℝ) (hQ : Measurable Q)
    (bQ : ∀ᵐ p ∂μ.prod μ, 0 ≤ Q p ∧ Q p ≤ (1:ℝ)/2)
    (rQ : ∀ᵐ x ∂μ, ∫ y, Q (x,y) ∂μ=(1:ℝ)/3)
    (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (bs : ∀ᵐ x ∂μ, s x=0 ∨ s x=1)
    (bt : ∀ᵐ x ∂μ, t x=0 ∨ t x=1)
    (hedge : ∀ᵐ p ∂μ.prod μ, 0 < Q p →
      ((t p.1=s p.2 ∧ t p.2=s p.1) ∨
       (t p.1=1-s p.2 ∧ t p.2=1-s p.1))) :
    (t =ᵐ[μ] s) ∨ (t =ᵐ[μ] (fun x => 1-s x)) := by
  let u : Ω → ℝ := fun x => (s x-t x)^2
  have hu : Measurable u := by fun_prop
  have bu : ∀ᵐ x ∂μ, u x=0 ∨ u x=1 := by
    filter_upwards [bs,bt] with x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [u,hx,hy]
  have hp : ∀ᵐ p ∂μ.prod μ, 0 < Q p → u p.1=u p.2 := by
    filter_upwards [hedge] with p hp
    intro hpos
    rcases hp hpos with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
      dsimp only [u] <;> rw [h1,h2] <;> ring
  have h := TwoPairDenseInvariant.binary_invariant_constant μ Q hQ
    ((1:ℝ)/2) ((1:ℝ)/3) bQ rQ (by norm_num) u hu bu hp
  rcases h with h | h
  · left
    filter_upwards [h] with x hx
    dsimp only [u] at hx
    nlinarith [sq_nonneg (s x-t x)]
  · right
    filter_upwards [h,bs,bt] with x hx hxs hxt
    rcases hxs with hxs | hxs <;> rcases hxt with hxt | hxt <;>
      simp_all [u]

lemma transport_cut_no_crossing
    (K : Ω × Ω → ℝ) (hK : Measurable K) (bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1)
    (k : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ=k)
    (s : Ω → ℝ) (hs : Measurable s) (bs : ∀ x, s x=0 ∨ s x=1)
    (t : Ω → ℝ) (ht : Measurable t) (bt : ∀ x, t x=0 ∨ t x=1)
    (he : ∀ᵐ x ∂μ, act μ K s x=k*t x) :
    ∀ᵐ p ∂μ.prod μ, 0 < K p → t p.1=s p.2 := by
  have hmeas : MeasurableSet {p : Ω × Ω | 0 < K p → t p.1=s p.2} :=
    (measurableSet_lt measurable_const hK).imp
      (measurableSet_eq_fun (ht.comp measurable_fst) (hs.comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [hr,he] with x hx hex
  have bs' (y : Ω) : 0 ≤ s y ∧ s y ≤ 1 := by rcases bs y with h | h <;> simp [h]
  have hiK : Integrable (fun y => K (x,y)) μ :=
    unit_integrable μ _ (by fun_prop) (fun y => bK (x,y))
  have hiKs : Integrable (fun y => K (x,y)*s y) μ :=
    unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bK _) (bs' _))
  rcases bt x with hsx | hsx
  · have hz : (∫ y, K (x,y)*s y ∂μ)=0 := by
      change (∫ y, K (x,y)*s y ∂μ)=k*t x at hex
      simpa [hsx] using hex
    have hzero := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => mul_nonneg (bK (x,y)).1 (bs' y).1)) hiKs).mp hz
    filter_upwards [hzero] with y hy
    intro hxy
    change K (x,y)*s y=0 at hy
    have hsy := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hxy)
    exact hsx.trans hsy.symm
  · have hic : Integrable (fun y => K (x,y)*(1-s y)) μ :=
      unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bK _)
        ⟨by linarith [(bs' y).2],by linarith [(bs' y).1]⟩)
    have hz : (∫ y, K (x,y)*(1-s y) ∂μ)=0 := by
      calc
        _ = ∫ y, K (x,y)-K (x,y)*s y ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y => by dsimp only; ring)
        _ = 0 := by
          rw [integral_sub hiK hiKs,hx]
          change (∫ y, K (x,y)*s y ∂μ)=k*t x at hex
          rw [hex,hsx]
          ring
    have hzero := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => mul_nonneg (bK (x,y)).1
        (by linarith [(bs' y).2]))) hic).mp hz
    filter_upwards [hzero] with y hy
    intro hxy
    change K (x,y)*(1-s y)=0 at hy
    have hsy := (mul_eq_zero.mp hy).resolve_left (ne_of_gt hxy)
    rw [hsx]
    linarith


end TwoPairBipartiteOrientation


end


-- Local module: TwoPairBipartiteTransport
section
open MeasureTheory
namespace TwoPairBipartiteTransport
open FourColorKernels TwoPairHalfSetOperator TwoPairBipartiteOrientation
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma row_transport
    (A B : Ω × Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (rA : ∀ᵐ x ∂μ, ∫ y, A (x,y) ∂μ=(1:ℝ)/6)
    (rB : ∀ᵐ x ∂μ, ∫ y, B (x,y) ∂μ=(1:ℝ)/6)
    (bQ : ∀ p, A p+B p ≤ (1:ℝ)/2)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ S=(1:ENNReal)/2)
    (hind : ∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 →
      comp μ A B p+comp μ B A p=0) :
    ∃ X : Set Ω, MeasurableSet X ∧ μ X=(1:ENNReal)/2 ∧
      ((oneSet X =ᵐ[μ] oneSet S) ∨
       (oneSet X =ᵐ[μ] (fun x => 1-oneSet S x))) ∧
      (∀ᵐ p ∂μ.prod μ, 0 < A p → oneSet X p.1=oneSet S p.2) ∧
      (∀ᵐ p ∂μ.prod μ, 0 < B p → 1-oneSet X p.1=oneSet S p.2) := by
  have hz := TwoPairFiniteReduction.images_orthogonal μ A B
    (fun p => comp μ A B p+comp μ B A p) hA hB bA bB sA
    (Filter.Eventually.of_forall (fun _ => rfl))
    (oneSet S) (oneSet_measurable S hS) (oneSet_binary S) hind
  obtain ⟨X,hX,mX,hAX,hBX,_⟩ := half_set_transport μ A B hA hB bA bB sA sB
    ((1:ℝ)/6) (by norm_num) rA rB S hS mS hz
  have ec (x : Ω) : oneSet Xᶜ x=1-oneSet X x := by
    classical
    by_cases hx : x ∈ X <;> simp [oneSet,hx]
  have ha := transport_cut_no_crossing μ A hA bA ((1:ℝ)/6) rA
    (oneSet S) (oneSet_measurable S hS) (oneSet_binary S)
    (oneSet X) (oneSet_measurable X hX) (oneSet_binary X) hAX
  have hb0 := transport_cut_no_crossing μ B hB bB ((1:ℝ)/6) rB
    (oneSet S) (oneSet_measurable S hS) (oneSet_binary S)
    (oneSet Xᶜ) (oneSet_measurable Xᶜ hX.compl) (oneSet_binary Xᶜ) hBX
  have hb : ∀ᵐ p ∂μ.prod μ, 0 < B p → 1-oneSet X p.1=oneSet S p.2 := by
    simpa only [ec] using hb0
  have has : ∀ᵐ p ∂μ.prod μ, 0 < A p → oneSet X p.2=oneSet S p.1 := by
    have h := Measure.measurePreserving_swap.quasiMeasurePreserving.ae ha
    filter_upwards [h] with p hp
    change (0 < A (p.2,p.1) → oneSet X p.2=oneSet S p.1) at hp
    simpa only [sA p.2 p.1] using hp
  have hbs : ∀ᵐ p ∂μ.prod μ, 0 < B p → 1-oneSet X p.2=oneSet S p.1 := by
    have h := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hb
    filter_upwards [h] with p hp
    change (0 < B (p.2,p.1) → 1-oneSet X p.2=oneSet S p.1) at hp
    simpa only [sB p.2 p.1] using hp
  have rq : ∀ᵐ x ∂μ, ∫ y, (A (x,y)+B (x,y)) ∂μ=(1:ℝ)/3 := by
    filter_upwards [rA,rB] with x ax bx
    rw [integral_add (unit_integrable μ _ (by fun_prop) (fun y => bA (x,y)))
      (unit_integrable μ _ (by fun_prop) (fun y => bB (x,y))),ax,bx]
    norm_num
  have hq : ∀ᵐ p ∂μ.prod μ, 0 < A p+B p →
      ((oneSet X p.1=oneSet S p.2 ∧ oneSet X p.2=oneSet S p.1) ∨
       (oneSet X p.1=1-oneSet S p.2 ∧ oneSet X p.2=1-oneSet S p.1)) := by
    filter_upwards [ha,hb,has,hbs] with p ap bp aps bps
    intro hp
    by_cases hap : 0 < A p
    · exact Or.inl ⟨ap hap,aps hap⟩
    · have hbp : 0 < B p := by linarith
      right
      constructor <;> linarith [bp hbp,bps hbp]
  have halign := orientation_alignment μ (fun p => A p+B p) (hA.add hB)
    (Filter.Eventually.of_forall (fun p => ⟨add_nonneg (bA p).1 (bB p).1,bQ p⟩)) rq
    (oneSet S) (oneSet X) (oneSet_measurable S hS) (oneSet_measurable X hX)
    (Filter.Eventually.of_forall (oneSet_binary S))
    (Filter.Eventually.of_forall (oneSet_binary X)) hq
  exact ⟨X,hX,mX,halign,ha,hb⟩
end TwoPairBipartiteTransport
end


-- Local module: TwoPairRankOneCycle
section
open MeasureTheory
namespace TwoPairRankOneCycle
open FourColorKernels TwoPairCycleReduction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma comp_mono_ae (F G A B : Ω × Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hA : Measurable A) (hB : Measurable B)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (hFA : F ≤ᵐ[μ.prod μ] A) (hGB : G ≤ᵐ[μ.prod μ] B) :
    comp μ F G ≤ᵐ[μ.prod μ] comp μ A B := by
  have hrow := Measure.ae_ae_of_ae_prod hFA
  have hcol : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, G (z,y) ≤ B (z,y) := by
    apply (Measure.ae_ae_comm (p := fun z y => G (z,y) ≤ B (z,y)) ?_).mp
      (Measure.ae_ae_of_ae_prod hGB)
    exact measurableSet_le hG hB
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (measurable_comp μ F G hF hG) (measurable_comp μ A B hA hB))).mpr
  filter_upwards [hrow] with x hx
  filter_upwards [hcol] with y hy
  apply integral_mono_ae
    (unit_integrable μ _ (by fun_prop) (fun z => mul_unit (bF _) (bG _)))
    (unit_integrable μ _ (by fun_prop) (fun z => mul_unit (bA _) (bB _)))
  filter_upwards [hx,hy] with z hz hzy
  exact mul_le_mul hz hzy (bG _).1 (bA _).1

/-- Exact sandwich identity for a directed rank-one bridge. -/
lemma rank_one_sandwich (u v : Ω → ℝ) (K : Ω × Ω → ℝ)
    (x y : Ω) :
    comp μ (fun p => u p.1*v p.2)
      (comp μ K (fun p => v p.1*u p.2)) (x,y) =
      u x*u y*(∫ z, ∫ w, v z*K (z,w)*v w ∂μ ∂μ) := by
  unfold comp
  have hi (z : Ω) : (∫ w, K (z,w)*(v w*u y) ∂μ)=
      (∫ w, K (z,w)*v w ∂μ)*u y := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => by dsimp only; ring)
  simp_rw [hi]
  calc
    _ = ∫ z, (u x*u y)*(v z*(∫ w, K (z,w)*v w ∂μ)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by dsimp only; ring)
    _ = u x*u y*(∫ z, v z*(∫ w, K (z,w)*v w ∂μ) ∂μ) := integral_const_mul _ _
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => by dsimp only; ring)

lemma bridge_cycle_lower (A C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (u v : Ω → ℝ) (hu : Measurable u) (hv : Measurable v)
    (bu : ∀ x, 0 ≤ u x ∧ u x ≤ 1) (bv : ∀ x, 0 ≤ v x ∧ v x ≤ 1)
    (hf : ∀ᵐ p ∂μ.prod μ, u p.1*v p.2 ≤ A p)
    (hg : ∀ᵐ p ∂μ.prod μ, v p.1*u p.2 ≤ A p) :
    (∫ z, ∫ w, v z*C (z,w)*v w ∂μ ∂μ) *
      (∫ p, u p.1*u p.2*D (p.2,p.1) ∂μ.prod μ) ≤
      closing4 μ A C A D := by
  let F : Ω × Ω → ℝ := fun p => u p.1*v p.2
  let G : Ω × Ω → ℝ := fun p => v p.1*u p.2
  have hF : Measurable F := by fun_prop
  have hG : Measurable G := by fun_prop
  have bF (p : Ω × Ω) : 0 ≤ F p ∧ F p ≤ 1 := mul_unit (bu _) (bv _)
  have bG (p : Ω × Ω) : 0 ≤ G p ∧ G p ≤ 1 := mul_unit (bv _) (bu _)
  have hCG := measurable_comp μ C G hC hG
  have hCA := measurable_comp μ C A hC hA
  have bCG := comp_bounds μ C G hC hG bC bG
  have bCA := comp_bounds μ C A hC hA bC bA
  have h1 := comp_mono_ae μ C G C A hC hG hC hA bC bG bC bA
    (Filter.Eventually.of_forall (fun _ => le_refl _)) hg
  have h2 := comp_mono_ae μ F (comp μ C G) A (comp μ C A)
    hF hCG hA hCA bF bCG bA bCA hf h1
  have hm1 := (measurable_comp μ F (comp μ C G) hF hCG).mul (hD.comp measurable_swap)
  have hm2 := (measurable_comp μ A (comp μ C A) hA hCA).mul (hD.comp measurable_swap)
  have bm1 := comp_bounds μ F (comp μ C G) hF hCG bF bCG
  have bm2 := comp_bounds μ A (comp μ C A) hA hCA bA bCA
  have hh := integral_mono_ae
    (unit_integrable (μ.prod μ) _ hm1 (fun p => mul_unit (bm1 p) (bD _)))
    (unit_integrable (μ.prod μ) _ hm2 (fun p => mul_unit (bm2 p) (bD _)))
    (h2.mono (fun p hp => mul_le_mul_of_nonneg_right hp (bD _).1))
  have he : (∫ p, comp μ F (comp μ C G) p*D (p.2,p.1) ∂μ.prod μ) =
      (∫ z, ∫ w, v z*C (z,w)*v w ∂μ ∂μ) *
      (∫ p, u p.1*u p.2*D (p.2,p.1) ∂μ.prod μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    have h := rank_one_sandwich μ u v C p.1 p.2
    change comp μ F (comp μ C G) (p.1,p.2) = _ at h
    dsimp only
    change comp μ F (comp μ C G) p = _ at h
    rw [h]
    ring
  change (∫ p, comp μ F (comp μ C G) p*D (p.2,p.1) ∂μ.prod μ) ≤
    (∫ p, comp μ A (comp μ C A) p*D (p.2,p.1) ∂μ.prod μ) at hh
  rw [he] at hh
  have he2 : (∫ p, comp μ A (comp μ C A) p*D (p.2,p.1) ∂μ.prod μ)=
      closing4 μ A C A D := by
    unfold closing4
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => mul_comm _ _)
  rwa [he2] at hh

lemma eigen_energy (K : Ω × Ω → ℝ) (v : Ω → ℝ) (d : ℝ)
    (he : ∀ᵐ z ∂μ, TwoPairHalfSetOperator.act μ K v z=d*v z) :
    (∫ z, ∫ w, v z*K (z,w)*v w ∂μ ∂μ)=d*(∫ z, (v z)^2 ∂μ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [he] with z hz
  calc
    _ = v z*(∫ w, K (z,w)*v w ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => by dsimp only; ring)
    _ = _ := by
      change (∫ w, K (z,w)*v w ∂μ)=d*v z at hz
      rw [hz]
      ring

lemma eigen_pair_energy (K : Ω × Ω → ℝ) (hK : Measurable K)
    (bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1) (sK : ∀ x y, K (x,y)=K (y,x))
    (u : Ω → ℝ) (hu : Measurable u) (bu : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (d : ℝ) (he : ∀ᵐ z ∂μ, TwoPairHalfSetOperator.act μ K u z=d*u z) :
    (∫ p, u p.1*u p.2*K (p.2,p.1) ∂μ.prod μ)=d*(∫ z, (u z)^2 ∂μ) := by
  have hi : Integrable (fun p : Ω × Ω => u p.1*u p.2*K (p.2,p.1)) (μ.prod μ) :=
    unit_integrable _ _ (by fun_prop) (fun p => mul_unit (mul_unit (bu _) (bu _)) (bK _))
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, ∫ y, u x*K (x,y)*u y ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by dsimp only; rw [sK y x]; ring)
    _ = _ := eigen_energy μ K u d he

lemma bridge_cycle_positive (A C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1) (sD : ∀ x y, D (x,y)=D (y,x))
    (u v : Ω → ℝ) (hu : Measurable u) (hv : Measurable v)
    (bu : ∀ x, 0 ≤ u x ∧ u x ≤ 1) (bv : ∀ x, 0 ≤ v x ∧ v x ≤ 1)
    (hf : ∀ᵐ p ∂μ.prod μ, u p.1*v p.2 ≤ A p)
    (hg : ∀ᵐ p ∂μ.prod μ, v p.1*u p.2 ≤ A p)
    (d e : ℝ) (hd : 0 < d) (he : 0 < e)
    (hc : ∀ᵐ z ∂μ, TwoPairHalfSetOperator.act μ C v z=d*v z)
    (hd' : ∀ᵐ z ∂μ, TwoPairHalfSetOperator.act μ D u z=e*u z)
    (pu : 0 < ∫ z, (u z)^2 ∂μ) (pv : 0 < ∫ z, (v z)^2 ∂μ) :
    0 < closing4 μ A C A D := by
  have h := bridge_cycle_lower μ A C D hA hC hD bA bC bD u v hu hv bu bv hf hg
  rw [eigen_energy μ C v d hc,eigen_pair_energy μ D hD bD sD u hu bu e hd'] at h
  exact lt_of_lt_of_le (mul_pos (mul_pos hd pv) (mul_pos he pu)) h

end TwoPairRankOneCycle




end


-- Local module: TwoPairJointCut
section
open MeasureTheory
namespace TwoPairJointCut
open FourColorKernels TwoPairHalfSetOperator TwoPairBipartiteOrientation
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma act_of_edge_invariance (K : Ω × Ω → ℝ) (hK : Measurable K)
    (bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1) (d : ℝ)
    (hr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ=d)
    (v : Ω → ℝ) (hv : Measurable v)
    (hp : ∀ᵐ p ∂μ.prod μ, 0 < K p → v p.1=v p.2) :
    ∀ᵐ x ∂μ, act μ K v x=d*v x := by
  filter_upwards [hr,Measure.ae_ae_of_ae_prod hp] with x hx hxp
  change (∫ y, K (x,y)*v y ∂μ)=d*v x
  calc
    _ = ∫ y, K (x,y)*v x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hxp] with y hy
      by_cases hpos : 0 < K (x,y)
      · rw [hy hpos]
      · have hz : K (x,y)=0 := by linarith [(bK (x,y)).1]
        simp [hz]
    _ = _ := by rw [integral_mul_const,hx]

lemma intersection_eigen (K : Ω × Ω → ℝ) (hK : Measurable K)
    (bK : ∀ p, 0 ≤ K p ∧ K p ≤ 1) (sK : ∀ x y, K (x,y)=K (y,x))
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ=d)
    (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (he : ∀ᵐ x ∂μ, act μ K s x=d*t x) :
    ∀ᵐ x ∂μ, act μ K (fun y => s y*t y) x=d*(s x*t x) := by
  have hp := transport_cut_no_crossing μ K hK bK d hr s hs bs t ht bt he
  have hps := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp
  apply act_of_edge_invariance μ K hK bK d hr (fun x => s x*t x) (hs.mul ht)
  filter_upwards [hp,hps] with p h1 h2
  intro hpos
  change (0 < K (p.2,p.1) → t p.2=s p.1) at h2
  have he1 := h1 hpos
  have he2 := h2 (by simpa only [sK p.2 p.1] using hpos)
  change s p.1*t p.1=s p.2*t p.2
  rw [he1,he2]
  ring
end TwoPairJointCut
end


-- Local module: TwoPairBinaryHalfCuts
section
open MeasureTheory
namespace TwoPairBinaryHalfCuts
open FourColorKernels
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma binary_equal_of_no_mismatch (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (hm : ∫ x, s x ∂μ=∫ x, t x ∂μ)
    (hz : ∀ᵐ x ∂μ, s x*(1-t x)=0) : t =ᵐ[μ] s := by
  have bss (x : Ω) : 0 ≤ s x ∧ s x ≤ 1 := by rcases bs x with h | h <;> simp [h]
  have btt (x : Ω) : 0 ≤ t x ∧ t x ≤ 1 := by rcases bt x with h | h <;> simp [h]
  have his := unit_integrable μ s hs bss
  have hit := unit_integrable μ t ht btt
  have hn : ∀ᵐ x ∂μ, 0 ≤ t x-s x := by
    filter_upwards [hz] with x hx
    rcases bs x with h1 | h1 <;> rcases bt x with h2 | h2 <;> simp_all
  have hi : (∫ x, t x-s x ∂μ)=0 := by
    rw [integral_sub hit his,hm]
    ring
  have hh := (integral_eq_zero_iff_of_nonneg_ae hn (hit.sub his)).mp hi
  filter_upwards [hh] with x hx
  exact sub_eq_zero.mp hx

lemma binary_square_zero (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ x, f x=0 ∨ f x=1) (hz : (∫ x, (f x)^2 ∂μ)=0) :
    f =ᵐ[μ] (fun _ => 0) := by
  have hb (x : Ω) : 0 ≤ (f x)^2 ∧ (f x)^2 ≤ 1 := by
    rcases bf x with h | h <;> simp [h]
  have hh := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x))
    (unit_integrable μ _ (hf.pow_const 2) hb)).mp hz
  filter_upwards [hh] with x hx
  change (f x)^2=0 at hx
  change f x=0
  nlinarith [sq_nonneg (f x)]

lemma half_cuts_extreme (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (ms : ∫ x, s x ∂μ=(1:ℝ)/2) (mt : ∫ x, t x ∂μ=(1:ℝ)/2)
    (hnot : ¬ ((0 < ∫ x, (s x*t x)^2 ∂μ) ∧
                (0 < ∫ x, (s x*(1-t x))^2 ∂μ))) :
    (t =ᵐ[μ] s) ∨ (t =ᵐ[μ] (fun x => 1-s x)) := by
  have b0 (x : Ω) : s x*t x=0 ∨ s x*t x=1 := by
    rcases bs x with h1 | h1 <;> rcases bt x with h2 | h2 <;> simp [h1,h2]
  have b1 (x : Ω) : s x*(1-t x)=0 ∨ s x*(1-t x)=1 := by
    rcases bs x with h1 | h1 <;> rcases bt x with h2 | h2 <;> simp [h1,h2]
  by_cases hp : 0 < ∫ x, (s x*t x)^2 ∂μ
  · left
    have hz : (∫ x, (s x*(1-t x))^2 ∂μ)=0 := by
      have hn : (0:ℝ) ≤ ∫ x, (s x*(1-t x))^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
      have hn' : ¬ 0 < ∫ x, (s x*(1-t x))^2 ∂μ := fun h => hnot ⟨hp,h⟩
      linarith
    exact binary_equal_of_no_mismatch μ s t hs ht bs bt (ms.trans mt.symm)
      (binary_square_zero μ _ (by fun_prop) b1 hz)
  · right
    have hz : (∫ x, (s x*t x)^2 ∂μ)=0 := by
      have hn : (0:ℝ) ≤ ∫ x, (s x*t x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
      linarith
    have hzero := binary_square_zero μ _ (by fun_prop) b0 hz
    have btc (x : Ω) : 1-t x=0 ∨ 1-t x=1 := by rcases bt x with h | h <;> simp [h]
    have hit := unit_integrable μ t ht (fun x => by rcases bt x with h | h <;> simp [h])
    have hmc : ∫ x, s x ∂μ=∫ x, (1-t x) ∂μ := by
      rw [integral_sub (integrable_const _) hit,mt,ms]
      simp
      norm_num
    have hh := binary_equal_of_no_mismatch μ s (fun x => 1-t x) hs (by fun_prop)
      bs btc hmc (by
        filter_upwards [hzero] with x hx
        change s x*t x=0 at hx
        simpa only [sub_sub_cancel] using hx)
    filter_upwards [hh] with x hx
    linarith
end TwoPairBinaryHalfCuts
end


-- Local module: TwoPairSingletonAlignment
section
open MeasureTheory
namespace TwoPairSingletonAlignment
open FourColorKernels TwoPairHalfSetOperator TwoPairCycleReduction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma alignment_from_bridge (A C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6)
    (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (ms : ∫ x, s x ∂μ=(1:ℝ)/2) (mt : ∫ x, t x ∂μ=(1:ℝ)/2)
    (hc : ∀ᵐ x ∂μ, act μ C s x=((1:ℝ)/6)*t x)
    (hd : ∀ᵐ x ∂μ, act μ D s x=((1:ℝ)/6)*(1-t x))
    (hb : ∀ᵐ p ∂μ.prod μ, s p.1=1 → s p.2=1 → t p.1≠t p.2 → A p=(1:ℝ)/2)
    (hz : closing4 μ A C A D=0) :
    (t =ᵐ[μ] s) ∨ (t =ᵐ[μ] (fun x => 1-s x)) := by
  let u : Ω → ℝ := fun x => (s x*(1-t x))/2
  let v : Ω → ℝ := fun x => s x*t x
  have hu : Measurable u := by fun_prop
  have hv : Measurable v := by fun_prop
  have bu (x : Ω) : 0 ≤ u x ∧ u x ≤ 1 := by
    rcases bs x with h1 | h1 <;> rcases bt x with h2 | h2 <;> norm_num [u,h1,h2]
  have bv (x : Ω) : 0 ≤ v x ∧ v x ≤ 1 := by
    rcases bs x with h1 | h1 <;> rcases bt x with h2 | h2 <;> norm_num [v,h1,h2]
  have bsm (x : Ω) : 0 ≤ s x*(1-t x) ∧ s x*(1-t x) ≤ 1 := by
    rcases bs x with h1 | h1 <;> rcases bt x with h2 | h2 <;> norm_num [h1,h2]
  have hcv := TwoPairJointCut.intersection_eigen μ C hC bC sC ((1:ℝ)/6) rC s t hs ht bs bt hc
  have btc (x : Ω) : 1-t x=0 ∨ 1-t x=1 := by rcases bt x with h | h <;> simp [h]
  have hdy := TwoPairJointCut.intersection_eigen μ D hD bD sD ((1:ℝ)/6) rD
    s (fun x => 1-t x) hs (by fun_prop) bs btc hd
  have hdu : ∀ᵐ x ∂μ, act μ D u x=((1:ℝ)/6)*u x := by
    filter_upwards [hdy] with x hx
    change (∫ y, D (x,y)*u y ∂μ)=_
    calc
      _ = (∫ y, D (x,y)*(s y*(1-t y)) ∂μ)/2 := by
        rw [← integral_div]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by dsimp only [u]; ring)
      _ = _ := by
        change (∫ y, D (x,y)*(s y*(1-t y)) ∂μ)=((1:ℝ)/6)*(s x*(1-t x)) at hx
        rw [hx]
        dsimp only [u]
        ring
  have hf : ∀ᵐ p ∂μ.prod μ, u p.1*v p.2 ≤ A p := by
    filter_upwards [hb] with p hp
    rcases bs p.1 with h1 | h1 <;> rcases bs p.2 with h2 | h2 <;>
      rcases bt p.1 with h3 | h3 <;> rcases bt p.2 with h4 | h4 <;>
      simp only [u,v,h1,h2,h3,h4] at hp ⊢ <;>
      norm_num at hp ⊢ <;> linarith [(bA p).1]
  have hg : ∀ᵐ p ∂μ.prod μ, v p.1*u p.2 ≤ A p := by
    filter_upwards [hb] with p hp
    rcases bs p.1 with h1 | h1 <;> rcases bs p.2 with h2 | h2 <;>
      rcases bt p.1 with h3 | h3 <;> rcases bt p.2 with h4 | h4 <;>
      simp only [u,v,h1,h2,h3,h4] at hp ⊢ <;>
      norm_num at hp ⊢ <;> linarith [(bA p).1]
  apply TwoPairBinaryHalfCuts.half_cuts_extreme μ s t hs ht bs bt ms mt
  intro hpos
  have pu : 0 < ∫ x, (u x)^2 ∂μ := by
    have he : (∫ x, (u x)^2 ∂μ)=((1:ℝ)/4)*(∫ x, (s x*(1-t x))^2 ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only [u]; ring)
    rw [he]
    exact mul_pos (by norm_num) hpos.2
  have hp := TwoPairRankOneCycle.bridge_cycle_positive μ A C D hA hC hD bA bC bD sD
    u v hu hv bu bv hf hg ((1:ℝ)/6) ((1:ℝ)/6) (by norm_num) (by norm_num)
    hcv hdu pu hpos.1
  rw [hz] at hp
  exact lt_irrefl _ hp
end TwoPairSingletonAlignment
end


-- Local module: TwoPairPaletteBridge
section
open MeasureTheory
namespace TwoPairPaletteBridge
open TwoPairHalfSetOperator TwoPairBipartiteOrientation
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma bridge_from_partition (A B C D : Ω × Ω → ℝ)
    (hC : Measurable C) (hD : Measurable D)
    (bB : ∀ p, 0 ≤ B p) (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6)
    (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (hc : ∀ᵐ x ∂μ, act μ C s x=((1:ℝ)/6)*t x)
    (hd : ∀ᵐ x ∂μ, act μ D s x=((1:ℝ)/6)*(1-t x))
    (hb : ∀ᵐ p ∂μ.prod μ, 0 < B p → s p.1=1-s p.2)
    (htotal : ∀ᵐ p ∂μ.prod μ, 2*A p+2*B p+C p+D p=1) :
    ∀ᵐ p ∂μ.prod μ, s p.1=1 → s p.2=1 → t p.1≠t p.2 → A p=(1:ℝ)/2 := by
  have ec := transport_cut_no_crossing μ C hC bC ((1:ℝ)/6) rC s hs bs t ht bt hc
  have btc (x : Ω) : 1-t x=0 ∨ 1-t x=1 := by rcases bt x with h | h <;> simp [h]
  have ed := transport_cut_no_crossing μ D hD bD ((1:ℝ)/6) rD s hs bs
    (fun x => 1-t x) (by fun_prop) btc hd
  have ecs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae ec
  have eds := Measure.measurePreserving_swap.quasiMeasurePreserving.ae ed
  filter_upwards [ec,ed,ecs,eds,hb,htotal] with p cp dp cps dps bp total
  intro sp sq tn
  have bz : B p=0 := by
    by_contra hn
    have hp : 0 < B p := lt_of_le_of_ne (bB p) (Ne.symm hn)
    have h := bp hp
    rw [sp,sq] at h
    norm_num at h
  have cz : C p=0 := by
    by_contra hn
    have hp : 0 < C p := lt_of_le_of_ne (bC p).1 (Ne.symm hn)
    have h1 := cp hp
    change (0 < C (p.2,p.1) → t p.2=s p.1) at cps
    have h2 := cps (by simpa only [sC p.2 p.1] using hp)
    exact tn (by rw [h1,h2,sp,sq])
  have dz : D p=0 := by
    by_contra hn
    have hp : 0 < D p := lt_of_le_of_ne (bD p).1 (Ne.symm hn)
    have h1 := dp hp
    change (0 < D (p.2,p.1) → 1-t p.2=s p.1) at dps
    have h2 := dps (by simpa only [sD p.2 p.1] using hp)
    apply tn
    rw [sq] at h1
    rw [sp] at h2
    linarith
  rw [bz,cz,dz] at total
  linarith
end TwoPairPaletteBridge
end


-- Local module: TwoPairParityPalette
section
open MeasureTheory
namespace TwoPairParityPalette
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def parity (s : Ω → ℝ) (p : Ω × Ω) : ℝ :=
  if s p.1=s p.2 then 1 else 0

lemma lift_fst_eq (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (he : t =ᵐ[μ] s) : ∀ᵐ p ∂μ.prod μ, t p.1=s p.1 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (ht.comp measurable_fst) (hs.comp measurable_fst))).mpr
  exact he.mono (fun x hx => Filter.Eventually.of_forall (fun _ => hx))

lemma orientations_from_transport (A B : Ω × Ω → ℝ)
    (s t : Ω → ℝ) (hs : Measurable s) (ht : Measurable t)
    (halign : (t =ᵐ[μ] s) ∨ (t =ᵐ[μ] (fun x => 1-s x)))
    (ha : ∀ᵐ p ∂μ.prod μ, 0 < A p → t p.1=s p.2)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 < B p → 1-t p.1=s p.2) :
    ((∀ᵐ p ∂μ.prod μ, 0 < A p → s p.1=s p.2) ∧
     (∀ᵐ p ∂μ.prod μ, 0 < B p → s p.1=1-s p.2)) ∨
    ((∀ᵐ p ∂μ.prod μ, 0 < B p → s p.1=s p.2) ∧
     (∀ᵐ p ∂μ.prod μ, 0 < A p → s p.1=1-s p.2)) := by
  rcases halign with h | h
  · have hh := lift_fst_eq μ s t hs ht h
    left
    constructor
    · filter_upwards [ha,hh] with p hp hq
      intro hpos
      rw [← hq]
      exact hp hpos
    · filter_upwards [hb,hh] with p hp hq
      intro hpos
      linarith [hp hpos]
  · have hh := lift_fst_eq μ (fun x => 1-s x) t (by fun_prop) ht h
    right
    constructor
    · filter_upwards [hb,hh] with p hp hq
      intro hpos
      linarith [hp hpos]
    · filter_upwards [ha,hh] with p hp hq
      intro hpos
      linarith [hp hpos]

lemma palette_of_edges (A B C D : Ω × Ω → ℝ)
    (bA : ∀ p, 0 ≤ A p) (bB : ∀ p, 0 ≤ B p)
    (bC : ∀ p, 0 ≤ C p) (bD : ∀ p, 0 ≤ D p)
    (s : Ω → ℝ) (bs : ∀ x, s x=0 ∨ s x=1)
    (ha : ∀ᵐ p ∂μ.prod μ, 0 < A p → s p.1=s p.2)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 < B p → s p.1=1-s p.2)
    (hc : ∀ᵐ p ∂μ.prod μ, 0 < C p → s p.1=s p.2)
    (hd : ∀ᵐ p ∂μ.prod μ, 0 < D p → s p.1=1-s p.2)
    (htotal : ∀ᵐ p ∂μ.prod μ, 2*A p+2*B p+C p+D p=1) :
    ∀ᵐ p ∂μ.prod μ, 2*A p+C p=parity s p := by
  filter_upwards [ha,hb,hc,hd,htotal] with p ap bp cp dp total
  by_cases he : s p.1=s p.2
  · have hn : s p.1≠1-s p.2 := by
      rcases bs p.2 with h | h <;> rw [he,h] <;> norm_num
    have bz : B p=0 := by
      by_contra hz
      exact hn (bp (lt_of_le_of_ne (bB p) (Ne.symm hz)))
    have dz : D p=0 := by
      by_contra hz
      exact hn (dp (lt_of_le_of_ne (bD p) (Ne.symm hz)))
    simp only [parity,if_pos he]
    rw [bz,dz] at total
    linarith
  · have az : A p=0 := by
      by_contra hz
      exact he (ap (lt_of_le_of_ne (bA p) (Ne.symm hz)))
    have cz : C p=0 := by
      by_contra hz
      exact he (cp (lt_of_le_of_ne (bC p) (Ne.symm hz)))
    simp [parity,he,az,cz]

lemma choose_palette (A B C D : Ω × Ω → ℝ)
    (bA : ∀ p, 0 ≤ A p) (bB : ∀ p, 0 ≤ B p)
    (bC : ∀ p, 0 ≤ C p) (bD : ∀ p, 0 ≤ D p)
    (s : Ω → ℝ) (bs : ∀ x, s x=0 ∨ s x=1)
    (hab : ((∀ᵐ p ∂μ.prod μ, 0 < A p → s p.1=s p.2) ∧
            (∀ᵐ p ∂μ.prod μ, 0 < B p → s p.1=1-s p.2)) ∨
           ((∀ᵐ p ∂μ.prod μ, 0 < B p → s p.1=s p.2) ∧
            (∀ᵐ p ∂μ.prod μ, 0 < A p → s p.1=1-s p.2)))
    (hcd : ((∀ᵐ p ∂μ.prod μ, 0 < C p → s p.1=s p.2) ∧
            (∀ᵐ p ∂μ.prod μ, 0 < D p → s p.1=1-s p.2)) ∨
           ((∀ᵐ p ∂μ.prod μ, 0 < D p → s p.1=s p.2) ∧
            (∀ᵐ p ∂μ.prod μ, 0 < C p → s p.1=1-s p.2)))
    (htotal : ∀ᵐ p ∂μ.prod μ, 2*A p+2*B p+C p+D p=1) :
    ∃ c : Bool, ((∀ᵐ p ∂μ.prod μ, 2*A p+(if c then D p else C p)=parity s p) ∨
      (∀ᵐ p ∂μ.prod μ, 2*A p+(if c then D p else C p)=1-parity s p)) := by
  have hswapCD : ∀ᵐ p ∂μ.prod μ, 2*A p+2*B p+D p+C p=1 :=
    htotal.mono (fun p hp => by linarith)
  have hswapAB : ∀ᵐ p ∂μ.prod μ, 2*B p+2*A p+C p+D p=1 :=
    htotal.mono (fun p hp => by linarith)
  have hswap : ∀ᵐ p ∂μ.prod μ, 2*B p+2*A p+D p+C p=1 :=
    htotal.mono (fun p hp => by linarith)
  rcases hab with ⟨ha,hb⟩ | ⟨hb,ha⟩ <;> rcases hcd with ⟨hc,hd⟩ | ⟨hd,hc⟩
  · exact ⟨false,Or.inl (by simpa using palette_of_edges μ A B C D bA bB bC bD s bs ha hb hc hd htotal)⟩
  · exact ⟨true,Or.inl (by simpa using palette_of_edges μ A B D C bA bB bD bC s bs ha hb hd hc hswapCD)⟩
  · refine ⟨true,Or.inr ?_⟩
    have h := palette_of_edges μ B A C D bB bA bC bD s bs hb ha hc hd hswapAB
    filter_upwards [h,htotal] with p hp hpt
    simp only [↓reduceIte]
    linarith
  · refine ⟨false,Or.inr ?_⟩
    have h := palette_of_edges μ B A D C bB bA bD bC s bs hb ha hd hc hswap
    filter_upwards [h,htotal] with p hp hpt
    simp only [Bool.false_eq_true,↓reduceIte]
    linarith
end TwoPairParityPalette

end


-- Local module: TwoPairBipartiteParity
section
open MeasureTheory
namespace TwoPairBipartiteParity
open FourColorKernels TwoPairHalfSetOperator TwoPairCycleReduction TwoPairParityPalette
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bipartite_parity (A B C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (rA : ∀ᵐ x ∂μ, ∫ y, A (x,y) ∂μ=(1:ℝ)/6)
    (rB : ∀ᵐ x ∂μ, ∫ y, B (x,y) ∂μ=(1:ℝ)/6)
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6)
    (bQ : ∀ p, A p+B p ≤ (1:ℝ)/2)
    (htotal : ∀ᵐ p ∂μ.prod μ, 2*A p+2*B p+C p+D p=1)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ S=(1:ENNReal)/2)
    (hP : ∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 →
      comp μ A B p+comp μ B A p=0)
    (hL : ∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 →
      comp μ C D p+comp μ D C p=0)
    (hzA : closing4 μ A C A D=0) (hzB : closing4 μ B C B D=0) :
    ∃ c : Bool, ((∀ᵐ p ∂μ.prod μ, 2*A p+(if c then D p else C p)=parity (oneSet S) p) ∨
      (∀ᵐ p ∂μ.prod μ, 2*A p+(if c then D p else C p)=1-parity (oneSet S) p)) := by
  obtain ⟨X,hX,mX,hXA,ha,hb⟩ := TwoPairBipartiteTransport.row_transport μ A B hA hB bA bB
    sA sB rA rB bQ S hS mS hP
  have hab := orientations_from_transport μ A B (oneSet S) (oneSet X)
    (oneSet_measurable S hS) (oneSet_measurable X hX) hXA ha hb
  have hi := TwoPairFiniteReduction.images_orthogonal μ C D
    (fun p => comp μ C D p+comp μ D C p) hC hD bC bD sC
    (Filter.Eventually.of_forall (fun _ => rfl))
    (oneSet S) (oneSet_measurable S hS) (oneSet_binary S) hL
  obtain ⟨U,hU,mU,hCU,hDU,_⟩ := half_set_transport μ C D hC hD bC bD sC sD
    ((1:ℝ)/6) (by norm_num) rC rD S hS mS hi
  have eu (x : Ω) : oneSet Uᶜ x=1-oneSet U x := by
    classical
    by_cases hx : x ∈ U <;> simp [oneSet,hx]
  have hDU' : ∀ᵐ x ∂μ, act μ D (oneSet S) x=((1:ℝ)/6)*(1-oneSet U x) := by
    filter_upwards [hDU] with x hx
    change act μ D (oneSet S) x=((1:ℝ)/6)*oneSet Uᶜ x at hx
    simpa only [eu] using hx
  have ms : ∫ x, oneSet S x ∂μ=(1:ℝ)/2 := by
    calc
      _ = μ.real S := integral_indicator_one hS
      _ = _ := by simp [measureReal_def,mS]
  have mu : ∫ x, oneSet U x ∂μ=(1:ℝ)/2 := by
    calc
      _ = μ.real U := integral_indicator_one hU
      _ = _ := by simp [measureReal_def,mU]
  have halign : (oneSet U =ᵐ[μ] oneSet S) ∨
      (oneSet U =ᵐ[μ] (fun x => 1-oneSet S x)) := by
    rcases hab with ⟨ha',hb'⟩ | ⟨hb',ha'⟩
    · have bridge := TwoPairPaletteBridge.bridge_from_partition μ A B C D hC hD
        (fun p => (bB p).1) bC bD sC sD rC rD
        (oneSet S) (oneSet U) (oneSet_measurable S hS) (oneSet_measurable U hU)
        (oneSet_binary S) (oneSet_binary U) hCU hDU' hb' htotal
      exact TwoPairSingletonAlignment.alignment_from_bridge μ A C D hA hC hD bA bC bD sC sD rC rD
        (oneSet S) (oneSet U) (oneSet_measurable S hS) (oneSet_measurable U hU)
        (oneSet_binary S) (oneSet_binary U) ms mu hCU hDU' bridge hzA
    · have ht' : ∀ᵐ p ∂μ.prod μ, 2*B p+2*A p+C p+D p=1 :=
        htotal.mono (fun p hp => by linarith)
      have bridge := TwoPairPaletteBridge.bridge_from_partition μ B A C D hC hD
        (fun p => (bA p).1) bC bD sC sD rC rD
        (oneSet S) (oneSet U) (oneSet_measurable S hS) (oneSet_measurable U hU)
        (oneSet_binary S) (oneSet_binary U) hCU hDU' ha' ht'
      exact TwoPairSingletonAlignment.alignment_from_bridge μ B C D hB hC hD bB bC bD sC sD rC rD
        (oneSet S) (oneSet U) (oneSet_measurable S hS) (oneSet_measurable U hU)
        (oneSet_binary S) (oneSet_binary U) ms mu hCU hDU' bridge hzB
  have ec := TwoPairBipartiteOrientation.transport_cut_no_crossing μ C hC bC ((1:ℝ)/6) rC
    (oneSet S) (oneSet_measurable S hS) (oneSet_binary S)
    (oneSet U) (oneSet_measurable U hU) (oneSet_binary U) hCU
  have ed0 := TwoPairBipartiteOrientation.transport_cut_no_crossing μ D hD bD ((1:ℝ)/6) rD
    (oneSet S) (oneSet_measurable S hS) (oneSet_binary S)
    (oneSet Uᶜ) (oneSet_measurable Uᶜ hU.compl) (oneSet_binary Uᶜ) hDU
  have ed : ∀ᵐ p ∂μ.prod μ, 0 < D p → 1-oneSet U p.1=oneSet S p.2 := by
    simpa only [eu] using ed0
  have hcd := orientations_from_transport μ C D (oneSet S) (oneSet U)
    (oneSet_measurable S hS) (oneSet_measurable U hU) halign ec ed
  exact choose_palette μ A B C D (fun p => (bA p).1) (fun p => (bB p).1)
    (fun p => (bC p).1) (fun p => (bD p).1) (oneSet S) (oneSet_binary S) hab hcd htotal
end TwoPairBipartiteParity
end


-- Local module: TwoPairCutIndependence
section
open MeasureTheory
namespace TwoPairCutIndependence
open TwoPairFiniteReduction TwoPairHalfSetOperator
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma cut_independence (P L : Ω × Ω → ℝ)
    (bP : ∀ p, 0 ≤ P p) (bL : ∀ p, 0 ≤ L p)
    (S : Set Ω)
    (hcut : supportKernel P =ᵐ[μ.prod μ] TwoPairSupportReconstruction.cross S)
    (hLP : ∀ᵐ p ∂μ.prod μ, 0 < L p → supportKernel P p=1) :
    (∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 → P p=0) ∧
    (∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 → L p=0) := by
  have hz : ∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 → supportKernel P p=0 := by
    filter_upwards [hcut] with p hp
    intro hs ht
    have h1 : p.1∈S := by by_contra hn; simp [oneSet,hn] at hs
    have h2 : p.2∈S := by by_contra hn; simp [oneSet,hn] at ht
    rw [hp]
    simp [TwoPairSupportReconstruction.cross,h1,h2]
  constructor
  · filter_upwards [hz] with p hp
    intro hs ht
    have h0 := hp hs ht
    by_contra hn
    have hpos : 0 < P p := lt_of_le_of_ne (bP p) (Ne.symm hn)
    simp [supportKernel,hpos] at h0
  · filter_upwards [hz,hLP] with p hp hq
    intro hs ht
    have h0 := hp hs ht
    by_contra hn
    have hpos : 0 < L p := lt_of_le_of_ne (bL p) (Ne.symm hn)
    have h1 := hq hpos
    rw [h0] at h1
    norm_num at h1

lemma parity_oneSet (S : Set Ω) (p : Ω × Ω) :
    TwoPairParityPalette.parity (oneSet S) p =
      (if (p.1∈S ↔ p.2∈S) then (1:ℝ) else 0) := by
  classical
  by_cases h1 : p.1∈S <;> by_cases h2 : p.2∈S <;>
    simp [TwoPairParityPalette.parity,oneSet,h1,h2]

lemma half_measure (S : Set Ω) (hm : μ.real S=(1:ℝ)/2) : μ S=(1:ENNReal)/2 := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ S) (by norm_num)).mp
  simpa only [measureReal_def,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hm
end TwoPairCutIndependence
end


-- Local module: TwoPairNormalizedCut
section
open MeasureTheory
namespace TwoPairNormalizedCut
open TwoPairStructuralReduction TwoPairFiniteReduction
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem normalized_cut_parity (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i,Measurable (W i)) (hb : ∀ i p,0≤W i p ∧ W i p≤1)
    (hs : ∀ i x y,W i (x,y)=W i (y,x))
    (hr : ∀ i,∀ᵐ x ∂μ,∫ y,W i (x,y) ∂μ=(1/6:ℝ))
    (hpart : ∀ p,2*W 0 p+2*W 1 p+W 2 p+W 3 p=1)
    (facts : NormalizedFacts μ W)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ.real S=(1:ℝ)/2)
    (hcut : supportKernel (mixed μ W) =ᵐ[μ.prod μ] TwoPairSupportReconstruction.cross S) :
    ∃ c : Bool,
      ((∀ᵐ p ∂μ.prod μ, 2*W 0 p+(if c then W 3 p else W 2 p)=
          (if (p.1∈S ↔ p.2∈S) then (1:ℝ) else 0)) ∨
       (∀ᵐ p ∂μ.prod μ, 2*W 0 p+(if c then W 3 p else W 2 p)=
          1-(if (p.1∈S ↔ p.2∈S) then (1:ℝ) else 0))) := by
  have hi := TwoPairCutIndependence.cut_independence μ (mixed μ W) (singletonMixed μ W)
    (fun p => (facts.p_cap p).1) (fun p => (facts.l_cap p).1) S hcut facts.adjacency
  have h := TwoPairBipartiteParity.bipartite_parity μ (W 0) (W 1) (W 2) (W 3)
    (hm 0) (hm 1) (hm 2) (hm 3) (hb 0) (hb 1) (hb 2) (hb 3)
    (hs 0) (hs 1) (hs 2) (hs 3) (hr 0) (hr 1) (hr 2) (hr 3)
    (fun p => (facts.q_cap p).2) (Filter.Eventually.of_forall hpart)
    S hS (TwoPairCutIndependence.half_measure μ S mS) hi.1 hi.2
    facts.four_cycles.2.1 facts.four_cycles.2.2.2
  obtain ⟨c,hc⟩ := h
  refine ⟨c,?_⟩
  simpa only [TwoPairCutIndependence.parity_oneSet] using hc
end TwoPairNormalizedCut
end


-- Local module: TwoPairPrismDescent
section
open MeasureTheory
open scoped BigOperators
namespace TwoPairPrismDescent
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Two equal maximal masses force a unit-bounded row to be the class indicator. -/
lemma saturated_row (f s : Ω → ℝ) (hf : Measurable f) (hs : Measurable s)
    (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (bs : ∀ x, 0 ≤ s x ∧ s x ≤ 1)
    (d : ℝ) (hr : (∫ x, f x ∂μ)=d) (hm : (∫ x, s x ∂μ)=d)
    (hi : (∫ x, f x*s x ∂μ)=d) : f =ᵐ[μ] s := by
  have iF := unit_integrable μ f hf bf
  have iS := unit_integrable μ s hs bs
  have iFS := unit_integrable μ (fun x => f x*s x) (hf.mul hs) (fun x => mul_unit (bf x) (bs x))
  have zF : (∫ x, f x-f x*s x ∂μ)=0 := by rw [integral_sub iF iFS,hr,hi]; ring
  have zS : (∫ x, s x-f x*s x ∂μ)=0 := by rw [integral_sub iS iFS,hm,hi]; ring
  have eF := (integral_eq_zero_iff_of_nonneg (fun x => by
    exact sub_nonneg.mpr (mul_le_of_le_one_right (bf x).1 (bs x).2)) (iF.sub iFS)).mp zF
  have eS := (integral_eq_zero_iff_of_nonneg (fun x => by
    exact sub_nonneg.mpr (mul_le_of_le_one_left (bs x).1 (bf x).2)) (iS.sub iFS)).mp zS
  filter_upwards [eF,eS] with x hx hy
  change f x-f x*s x=0 at hx
  change s x-f x*s x=0 at hy
  linarith

lemma cross_flux_energy (C : Ω × Ω → ℝ) (s t : Ω → ℝ)
    (hC : Measurable C) (hs : Measurable s) (ht : Measurable t)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bs : ∀ x, 0 ≤ s x ∧ s x ≤ 1) (bt : ∀ x, 0 ≤ t x ∧ t x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) :
    (∫ p, s p.1*comp μ C C p*t p.2 ∂μ.prod μ)=
      ∫ z, act μ C s z*act μ C t z ∂μ := by
  have hCC := measurable_comp μ C C hC hC
  have bCC := comp_bounds μ C C hC hC bC bC
  have hCt := measurable_act μ C t hC ht
  have bCt := act_bounds μ C t hC ht bC bt
  have hi := unit_integrable (μ.prod μ) (fun p => s p.1*comp μ C C p*t p.2)
    (by fun_prop) (fun p => mul_unit (mul_unit (bs p.1) (bCC p)) (bt p.2))
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, s x*act μ C (act μ C t) x ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [← act_comp_square μ C t hC ht bC bt x]
      change (∫ y, s x*comp μ C C (x,y)*t y ∂μ)=s x*∫ y, comp μ C C (x,y)*t y ∂μ
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by dsimp only; ring)
    _ = ∫ x, act μ C t x*act μ C s x ∂μ :=
      act_pairing μ C s (act μ C t) hC hs hCt bC bs bCt sC
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

/-- This is obtained from actual square-confinement, not assumed image orthogonality. -/
lemma cross_flux_zero (C : Ω × Ω → ℝ) (s t : Ω → ℝ)
    (hC : Measurable C) (hs : Measurable s) (ht : Measurable t)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bs : ∀ x, 0 ≤ s x ∧ s x ≤ 1) (bt : ∀ x, 0 ≤ t x ∧ t x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hz : ∀ᵐ p ∂μ.prod μ, s p.1*comp μ C C p*t p.2=0) :
    ∀ᵐ z ∂μ, act μ C s z*act μ C t z=0 := by
  have hm := (measurable_act μ C s hC hs).mul (measurable_act μ C t hC ht)
  have hb (z : Ω) := mul_unit (act_bounds μ C s hC hs bC bs z) (act_bounds μ C t hC ht bC bt z)
  have hi : (∫ z, act μ C s z*act μ C t z ∂μ)=0 := by
    rw [← cross_flux_energy μ C s t hC hs ht bC bs bt sC,integral_congr_ae hz,integral_zero]
  exact (integral_eq_zero_iff_of_nonneg (fun z => (hb z).1)
    (unit_integrable μ _ hm hb)).mp hi

/-- Finite class indicators with square-confinement reconstruct every kernel row.
The class count is arbitrary; the prism uses six classes and d=1/6. -/
theorem rows_are_whole_classes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Ω × Ω → ℝ) (s : ι → Ω → ℝ)
    (hC : Measurable C) (hs : ∀ i, Measurable (s i))
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bs : ∀ i x, 0 ≤ s i x ∧ s i x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (d : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hpartition : ∀ x, ∑ i, s i x=1)
    (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (hconf : ∀ i j, i ≠ j → ∀ᵐ p ∂μ.prod μ,
      s i p.1*comp μ C C p*s j p.2=0) :
    ∀ᵐ x ∂μ, ∃ i, (fun y => C (x,y)) =ᵐ[μ] s i := by
  have hflux : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → act μ C (s i) x*act μ C (s j) x=0 := by
    apply (ae_all_iff).mpr
    intro i
    apply (ae_all_iff).mpr
    intro j
    by_cases hij : i=j
    · exact Filter.Eventually.of_forall (fun x hn => (hn hij).elim)
    · exact (cross_flux_zero μ C (s i) (s j) hC (hs i) (hs j) bC (bs i) (bs j) sC (hconf i j hij)).mono
        (fun x hx _ => hx)
  filter_upwards [hr,hflux] with x hx hpair
  have hsum : ∑ i, act μ C (s i) x=d := by
    unfold act
    rw [← integral_finsetSum _ (fun i _ =>
      unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bC (x,y)) (bs i y)))]
    calc
      _ = ∫ y, C (x,y) ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro y
        dsimp only
        rw [← Finset.mul_sum,hpartition y,mul_one]
      _ = d := hx
  have bn (i : ι) : 0 ≤ act μ C (s i) x := (act_bounds μ C (s i) hC (hs i) bC (bs i) x).1
  have hex : ∃ i, 0 < act μ C (s i) x := by
    by_contra hn
    have hz : ∀ i, act μ C (s i) x=0 := by
      intro i
      have hni : ¬ 0 < act μ C (s i) x := fun hi => hn ⟨i,hi⟩
      linarith [bn i]
    simp only [hz,Finset.sum_const_zero] at hsum
    linarith
  obtain ⟨i,hi⟩ := hex
  have hothers (j : ι) (hji : j ≠ i) : act μ C (s j) x=0 :=
    (mul_eq_zero.mp (hpair i j (Ne.symm hji))).resolve_left (ne_of_gt hi)
  have hiMass : act μ C (s i) x=d := by
    rw [Finset.sum_eq_single i (fun j _ hji => hothers j hji) (by simp)] at hsum
    exact hsum
  refine ⟨i,saturated_row μ (fun y => C (x,y)) (s i) (by fun_prop) (hs i)
    (fun y => bC (x,y)) (bs i) d hx (hm i) hiMass⟩

lemma class_gram {ι : Type*} [DecidableEq ι] (s : ι → Ω → ℝ)
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (d : ℝ) (hm : ∀ i, (∫ x, s i x ∂μ)=d) (i j : ι) :
    (∫ x, s i x*s j x ∂μ)=if i=j then d else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl,← hm i]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change s i x*s i x=s i x
    rcases bs i x with hx | hx <;> rw [hx] <;> norm_num
  · rw [if_neg hij]
    calc
      _ = ∫ x, (0:ℝ) ∂μ := integral_congr_ae (Filter.Eventually.of_forall (orth i j hij))
      _ = 0 := by simp

lemma positive_class_witness (s : Ω → ℝ) (bs : ∀ x, s x=0 ∨ s x=1)
    (d : ℝ) (hd : 0 < d) (hm : (∫ x, s x ∂μ)=d)
    (Good : Ω → Prop) (hg : ∀ᵐ x ∂μ, Good x) :
    ∃ x, s x=1 ∧ Good x := by
  by_contra hn
  have he : s =ᵐ[μ] fun _ => 0 := by
    filter_upwards [hg] with x hx
    rcases bs x with h0 | h1
    · exact h0
    · exact (hn ⟨x,h1,hx⟩).elim
  have hi : (∫ x, s x ∂μ)=0 := by rw [integral_congr_ae he,integral_zero]
  linarith

/-- Reversing reconstructed rows gives the whole target set as a row on each class. -/
lemma dual_rows {ι : Type*} [DecidableEq ι]
    (C : Ω × Ω → ℝ) (s : ι → Ω → ℝ)
    (hC : Measurable C) (hs : ∀ i, Measurable (s i))
    (sC : ∀ x y, C (x,y)=C (y,x))
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (d : ℝ) (hd : 0 < d)
    (gram : ∀ i j, (∫ x, s i x*s j x ∂μ)=if i=j then d else 0)
    (hrows : ∀ᵐ x ∂μ, ∃ j, (fun y => C (x,y)) =ᵐ[μ] s j) (i : ι) :
    ∀ᵐ y ∂μ, s i y=1 → (fun x => C (y,x)) =ᵐ[μ] (fun x => act μ C (s i) x/d) := by
  have he : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, s i y=1 → C (x,y)=act μ C (s i) x/d := by
    filter_upwards [hrows] with x hx
    obtain ⟨j,hj⟩ := hx
    have hflux : act μ C (s i) x=if j=i then d else 0 := by
      unfold act
      rw [integral_congr_ae (hj.mono (fun y hy => congrArg (fun r => r*s i y) hy)),gram j i]
    filter_upwards [hj] with y hy
    intro hi
    by_cases hji : j=i
    · subst j
      rw [hflux,if_pos rfl,div_self (ne_of_gt hd),hy,hi]
    · have hjzero : s j y=0 := by
        have hz := orth j i hji y
        rw [hi,mul_one] at hz
        exact hz
      rw [hflux,if_neg hji,zero_div,hy,hjzero]
  have he' : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, s i y=1 → C (x,y)=act μ C (s i) x/d := by
    apply (Measure.ae_ae_comm (p := fun x y => s i y=1 → C (x,y)=act μ C (s i) x/d) ?_).mp he
    exact (measurableSet_eq_fun ((hs i).comp measurable_snd) measurable_const).imp
      (measurableSet_eq_fun hC (((measurable_act μ C (s i) hC (hs i)).div_const d).comp measurable_fst))
  filter_upwards [he'] with y hy
  intro hi
  filter_upwards [hy] with x hx
  rw [sC y x]
  exact hx hi

/-- A symmetric kernel whose rows are equal positive disjoint class indicators
is reconstructed by an involution of the original classes. -/
theorem reconstruct_involution {ι : Type*} [DecidableEq ι]
    (C : Ω × Ω → ℝ) (s : ι → Ω → ℝ)
    (hC : Measurable C) (hs : ∀ i, Measurable (s i))
    (sC : ∀ x y, C (x,y)=C (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (d : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hrows : ∀ᵐ x ∂μ, ∃ j, (fun y => C (x,y)) =ᵐ[μ] s j) :
    ∃ c : ι → ι, Function.Involutive c ∧
      ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i) := by
  classical
  have gram := class_gram μ s bs orth d hm
  have hdual := dual_rows μ C s hC hs sC orth d hd gram hrows
  have hex (i : ι) : ∃ j, (fun x => act μ C (s i) x/d) =ᵐ[μ] s j := by
    obtain ⟨x,hix,hx⟩ := positive_class_witness μ (s i) (bs i) d hd (hm i)
      (fun x => (s i x=1 → (fun y => C (x,y)) =ᵐ[μ] (fun y => act μ C (s i) y/d)) ∧
        ∃ j, (fun y => C (x,y)) =ᵐ[μ] s j) ((hdual i).and hrows)
    obtain ⟨j,hj⟩ := hx.2
    exact ⟨j,(hx.1 hix).symm.trans hj⟩
  choose c hc using hex
  have hmap (i : ι) : ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i) := by
    filter_upwards [hdual i] with x hx
    intro hi
    exact (hx hi).trans (hc i)
  refine ⟨c,?_,hmap⟩
  intro i
  obtain ⟨x,hix,hx⟩ := positive_class_witness μ (s i) (bs i) d hd (hm i)
    (fun x => (s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i)) ∧
      act μ C (s (c i)) x/d=s (c (c i)) x) ((hmap i).and (hc (c i)))
  have hflux : act μ C (s (c i)) x=d := by
    unfold act
    rw [integral_congr_ae ((hx.1 hix).mono (fun y hy => congrArg (fun r => r*s (c i) y) hy)),gram (c i) (c i),if_pos rfl]
  have hone : s (c (c i)) x=1 := by
    rw [hflux,div_self (ne_of_gt hd)] at hx
    exact hx.2.symm
  by_contra hne
  have hz := orth (c (c i)) i hne x
  rw [hone,hix] at hz
  norm_num at hz


/-- Actual square-confinement, regularity and an equal measurable partition suffice
for the full singleton-kernel involution reconstruction. -/
theorem square_confined_involution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Ω × Ω → ℝ) (s : ι → Ω → ℝ)
    (hC : Measurable C) (hs : ∀ i, Measurable (s i))
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (hpartition : ∀ x, ∑ i, s i x=1)
    (d : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (hconf : ∀ i j, i ≠ j → ∀ᵐ p ∂μ.prod μ,
      s i p.1*comp μ C C p*s j p.2=0) :
    ∃ c : ι → ι, Function.Involutive c ∧
      ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i) := by
  have bu (i : ι) (x : Ω) : 0 ≤ s i x ∧ s i x ≤ 1 := by
    rcases bs i x with hx | hx <;> rw [hx] <;> norm_num
  exact reconstruct_involution μ C s hC hs sC bs orth d hd hm
    (rows_are_whole_classes μ C s hC hs bC bu sC d hd hm hpartition hr hconf)

end TwoPairPrismDescent


end


-- Local module: FourColorKernelMatrix
section
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
end


-- Local module: FourColorCycleMatrix
section
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
end


-- Local module: TwoPairPrismCylinder
section
open MeasureTheory
namespace TwoPairPrismCylinder
open FourColorKernels TwoPairPrismDescent TwoPairDoubledDisjoint
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma cycle4_zero_iff (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    cycle4 μ (W 0) (W 1) (W 2) (W 3)=0 ↔
      ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ᵐ u ∂μ,
        W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x)=0 := by
  unfold cycle4
  rw [unit_zero_iff μ (fun x => ∫ y, ∫ z, ∫ u, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x) ∂μ ∂μ ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with x
  rw [unit_zero_iff μ (fun y => ∫ z, ∫ u, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x) ∂μ ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with y
  rw [unit_zero_iff μ (fun z => ∫ u, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x) ∂μ) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with z
  rw [unit_zero_iff μ (fun u => W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x)) (by fun_prop) (by
    intro p
    repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]

/-- A positive cylinder in four positive classes gives an actual nonzero C4.
Repeated class indices are allowed; the four integration variables remain independent. -/
theorem four_class_cycle_nonzero (W : Fin 4 → Ω × Ω → ℝ) (s : Fin 4 → Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (d a : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) (ha : ∀ i, 0 < a i)
    (hm : ∀ i, (∫ x, s i x ∂μ)=d i)
    (e0 : ∀ᵐ p ∂μ.prod μ, s 0 p.1=1 → s 1 p.2=1 → W 0 p=a 0)
    (e1 : ∀ᵐ p ∂μ.prod μ, s 1 p.1=1 → s 2 p.2=1 → W 1 p=a 1)
    (e2 : ∀ᵐ p ∂μ.prod μ, s 2 p.1=1 → s 3 p.2=1 → W 2 p=a 2)
    (e3 : ∀ᵐ p ∂μ.prod μ, s 3 p.1=1 → s 0 p.2=1 → W 3 p=a 3) :
    cycle4 μ (W 0) (W 1) (W 2) (W 3) ≠ 0 := by
  intro hz
  have hzero := (cycle4_zero_iff μ W hW bW).mp hz
  have he0 := Measure.ae_ae_of_ae_prod e0
  have he1 := Measure.ae_ae_of_ae_prod e1
  have he2 := Measure.ae_ae_of_ae_prod e2
  have he3 := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae e3)
  obtain ⟨x,hx,hgx⟩ := positive_class_witness μ (s 0) (bs 0) (d 0) (hd 0) (hm 0)
    (fun x => (∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ᵐ u ∂μ, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x)=0) ∧
      (∀ᵐ y ∂μ, s 0 x=1 → s 1 y=1 → W 0 (x,y)=a 0) ∧
      (∀ᵐ u ∂μ, s 3 u=1 → s 0 x=1 → W 3 (u,x)=a 3)) (hzero.and (he0.and he3))
  obtain ⟨y,hy,hgy⟩ := positive_class_witness μ (s 1) (bs 1) (d 1) (hd 1) (hm 1)
    (fun y => (∀ᵐ z ∂μ, ∀ᵐ u ∂μ, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x)=0) ∧
      (s 0 x=1 → s 1 y=1 → W 0 (x,y)=a 0) ∧
      (∀ᵐ z ∂μ, s 1 y=1 → s 2 z=1 → W 1 (y,z)=a 1)) (hgx.1.and (hgx.2.1.and he1))
  obtain ⟨z,hz,hgz⟩ := positive_class_witness μ (s 2) (bs 2) (d 2) (hd 2) (hm 2)
    (fun z => (∀ᵐ u ∂μ, W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x)=0) ∧
      (s 1 y=1 → s 2 z=1 → W 1 (y,z)=a 1) ∧
      (∀ᵐ u ∂μ, s 2 z=1 → s 3 u=1 → W 2 (z,u)=a 2)) (hgy.1.and (hgy.2.2.and he2))
  obtain ⟨u,hu,hgu⟩ := positive_class_witness μ (s 3) (bs 3) (d 3) (hd 3) (hm 3)
    (fun u => W 0 (x,y)*W 1 (y,z)*W 2 (z,u)*W 3 (u,x)=0 ∧
      (s 2 z=1 → s 3 u=1 → W 2 (z,u)=a 2) ∧
      (s 3 u=1 → s 0 x=1 → W 3 (u,x)=a 3)) (hgz.1.and (hgz.2.2.and hgx.2.2))
  have hh := hgu.1
  rw [hgy.2.1 hx hy,hgz.2.1 hy hz,hgu.2.1 hz hu,hgu.2.2 hu hx] at hh
  exact (ne_of_gt (mul_pos (mul_pos (mul_pos (ha 0) (ha 1)) (ha 2)) (ha 3))) hh

lemma closing4_eq_cycle4 (A B C D : Ω × Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x)) :
    TwoPairCycleReduction.closing4 μ A B C D=cycle4 μ A B C D := by
  rw [TwoPairFourCycleProducts.closing4_pairing μ A B C D hA hB hC hD bA bB bC bD]
  have he : (fun p : Ω × Ω => comp μ C D (p.2,p.1))=comp μ D C := by
    funext p
    exact comp_swap μ C D sC sD p.2 p.1
  have hh : (∫ p, comp μ A B p*comp μ C D (p.2,p.1) ∂μ.prod μ)=
      ∫ p, comp μ A B p*comp μ D C p ∂μ.prod μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => congrArg (fun x => comp μ A B p*x) (congrFun he p))
  rw [hh]
  exact FourColorCycleMatrix.comp_pair_cycle (μ := μ) A B D C hA hB hD hC bA bB bD bC sD sC
end TwoPairPrismCylinder
end


-- Local module: TwoPairPrismBits
section

namespace TwoPairPrismBits

/-- Three pairwise opposite matching shifts cannot occur on three pairs. -/
theorem identity_shifts_impossible (a b c : ZMod 2)
    (hab : a + b = 1) (hac : a + c = 1) (hbc : b + c = 1) : False := by
  have h : b = c := add_left_cancel (hab.trans hac.symm)
  subst c
  have hz : b + b = 0 := by fin_cases b <;> decide
  have : (0 : ZMod 2) = 1 := hz.symm.trans hbc
  exact zero_ne_one this

/-- The three rectangle equations force opposite own-pair shifts. -/
theorem own_shifts_opposite (e_i e_j f_i f_j : ZMod 2)
    (hi : e_i + f_i = 1) (hj : e_j + f_j = 1)
    (hk : f_i + f_j = 1) : e_i + e_j = 1 := by
  fin_cases e_i <;> fin_cases e_j <;> fin_cases f_i <;> fin_cases f_j <;> revert hi hj hk <;> decide

/-- Following A,C,A,D returns to the starting bit in the transposition case. -/
theorem alternating_cycle_shift_zero (e_i e_j f_i f_j c : ZMod 2)
    (hi : e_i + f_i = 1) (hj : e_j + f_j = 1)
    (hk : f_i + f_j = 1) : e_i + c + e_j + (c + 1) = 0 := by
  have he := own_shifts_opposite e_i e_j f_i f_j hi hj hk
  fin_cases e_i <;> fin_cases e_j <;> fin_cases c <;> revert he <;> decide

/-- The two complementary own-pair shifts give the same closed bit walk. -/
theorem complementary_cycle_shift_zero (e_i e_j f_i f_j c : ZMod 2)
    (hi : e_i + f_i = 1) (hj : e_j + f_j = 1)
    (hk : f_i + f_j = 1) : (e_i + 1) + c + (e_j + 1) + (c + 1) = 0 := by
  have he := own_shifts_opposite e_i e_j f_i f_j hi hj hk
  fin_cases e_i <;> fin_cases e_j <;> fin_cases c <;> revert he <;> decide

theorem four_cylinders_exact :
    (4 : ℝ) * (1 / 2) ^ 2 * (1 / 6) ^ 4 = 1 / 1296 := by norm_num

theorem four_cylinders_positive :
    (0 : ℝ) < 4 * (1 / 2) ^ 2 * (1 / 6) ^ 4 := by norm_num


end TwoPairPrismBits
end


-- Local module: TwoPairPrismKernelClassification
section
open MeasureTheory
namespace TwoPairPrismKernelClassification
open FourColorKernels TwoPairHalfSetOperator TwoPairPrismDescent
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma class_flux_from_rows (C : Ω × Ω → ℝ) (s t : Ω → ℝ)
    (hC : Measurable C) (hs : Measurable s) (ht : Measurable t)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (bs : ∀ x, s x=0 ∨ s x=1) (d : ℝ) (hm : (∫ x, s x ∂μ)=d)
    (hr : ∀ᵐ x ∂μ, s x=1 → (fun y => C (x,y)) =ᵐ[μ] t) :
    act μ C s =ᵐ[μ] (fun y => d*t y) := by
  have he : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, C (x,y)*s x=s x*t y := by
    filter_upwards [hr] with x hx
    rcases bs x with h0 | h1
    · exact Filter.Eventually.of_forall (fun y => by rw [h0,mul_zero,zero_mul])
    · filter_upwards [hx h1] with y hy
      rw [h1,hy,mul_one,one_mul]
  have he' : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, C (x,y)*s x=s x*t y := by
    apply (Measure.ae_ae_comm (p := fun x y => C (x,y)*s x=s x*t y) ?_).mp he
    exact measurableSet_eq_fun (hC.mul (hs.comp measurable_fst))
      ((hs.comp measurable_fst).mul (ht.comp measurable_snd))
  filter_upwards [he'] with y hy
  change (∫ x, C (y,x)*s x ∂μ)=d*t y
  calc
    _ = ∫ x, s x*t y ∂μ := by
      apply integral_congr_ae
      filter_upwards [hy] with x hx
      simpa only [sC y x] using hx
    _ = _ := by rw [integral_mul_const,hm]

lemma composition_class_rows {ι : Type*}
    (C D : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (c e : ι → ι)
    (hD : Measurable D) (hs : ∀ i, Measurable (s i))
    (sD : ∀ x y, D (x,y)=D (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1) (d : ℝ) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (rC : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i))
    (rD : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => D (x,y)) =ᵐ[μ] s (e i)) :
    ∀ i, ∀ᵐ x ∂μ, s i x=1 →
      (fun y => comp μ C D (x,y)) =ᵐ[μ] (fun y => d*s (e (c i)) y) := by
  intro i
  have hf := class_flux_from_rows μ D (s (c i)) (s (e (c i))) hD (hs (c i))
    (hs (e (c i))) sD (bs (c i)) d (hm (c i)) (rD (c i))
  filter_upwards [rC i] with x hx
  intro hi
  filter_upwards [hf] with y hy
  change (∫ z, C (x,z)*D (z,y) ∂μ)=d*s (e (c i)) y
  calc
    _ = act μ D (s (c i)) y := by
      apply integral_congr_ae
      filter_upwards [hx hi] with z hz
      rw [hz,sD z y,mul_comm]
    _ = _ := hy

/-- Actual antipodal support of CD+DC identifies the composed class maps. -/
theorem composition_maps_antipodal {ι : Type*} [DecidableEq ι]
    (C D : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (c e τ : ι → ι)
    (hC : Measurable C) (hD : Measurable D) (hs : ∀ i, Measurable (s i))
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1) (d : ℝ) (hd : 0 < d)
    (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (rC : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i))
    (rD : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => D (x,y)) =ᵐ[μ] s (e i))
    (hz : ∀ i j, j ≠ τ i → ∀ᵐ p ∂μ.prod μ,
      s i p.1*(comp μ C D p+comp μ D C p)*s j p.2=0) :
    (∀ i, e (c i)=τ i) ∧ (∀ i, c (e i)=τ i) := by
  have rCD := composition_class_rows μ C D s c e hD hs sD bs d hm rC rD
  have rDC := composition_class_rows μ D C s e c hC hs sC bs d hm rD rC
  have one (F G : Ω × Ω → ℝ) (a : ι → ι)
      (bG : ∀ p, 0 ≤ G p)
      (rr : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => F (x,y)) =ᵐ[μ] (fun y => d*s (a i) y))
      (zz : ∀ i j, j ≠ τ i → ∀ᵐ p ∂μ.prod μ, s i p.1*(F p+G p)*s j p.2=0) :
      ∀ i, a i=τ i := by
    intro i
    by_contra hn
    have he := Measure.ae_ae_of_ae_prod (zz i (a i) hn)
    obtain ⟨x,hix,hx⟩ := positive_class_witness μ (s i) (bs i) d hd (hm i)
      (fun x => (s i x=1 → (fun y => F (x,y)) =ᵐ[μ] (fun y => d*s (a i) y)) ∧
        ∀ᵐ y ∂μ, s i x*(F (x,y)+G (x,y))*s (a i) y=0) ((rr i).and he)
    obtain ⟨y,hjy,hy⟩ := positive_class_witness μ (s (a i)) (bs (a i)) d hd (hm (a i))
      (fun y => F (x,y)=d*s (a i) y ∧ s i x*(F (x,y)+G (x,y))*s (a i) y=0)
      ((hx.1 hix).and hx.2)
    have hzero := hy.2
    rw [hix,hjy,one_mul,mul_one,hy.1,hjy,mul_one] at hzero
    linarith [bG (x,y)]
  constructor
  · exact one (comp μ C D) (comp μ D C) (fun i => e (c i))
      (fun p => (comp_bounds μ D C hD hC bD bC p).1) rCD hz
  · apply one (comp μ D C) (comp μ C D) (fun i => c (e i))
      (fun p => (comp_bounds μ C D hC hD bC bD p).1) rDC
    intro i j hij
    simpa only [add_comm] using hz i j hij
end TwoPairPrismKernelClassification
end


-- Local module: TwoPairPrismABBlocks
section
open MeasureTheory
namespace TwoPairPrismABBlocks
open FourColorKernels TwoPairHalfSetOperator TwoPairPrismDescent
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma weighted_zero (f s : Ω → ℝ) (hf : Measurable f) (hs : Measurable s)
    (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (bs : ∀ x, s x=0 ∨ s x=1)
    (hz : (∫ x, f x*s x ∂μ)=0) : ∀ᵐ x ∂μ, s x=1 → f x=0 := by
  have bu (x : Ω) : 0 ≤ s x ∧ s x ≤ 1 := by rcases bs x with h | h <;> simp [h]
  have he := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (bf x).1 (bu x).1)
    (unit_integrable μ _ (hf.mul hs) (fun x => mul_unit (bf x) (bu x)))).mp hz
  filter_upwards [he] with x hx
  intro hi
  change f x*s x=0 at hx
  simpa only [hi,mul_one] using hx

lemma split_row_constant (f g s : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hs : Measurable s)
    (bf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (bg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (bs : ∀ x, s x=0 ∨ s x=1) (d q : ℝ) (hd : 0 < d)
    (hm : (∫ x, s x ∂μ)=d)
    (hsum : ∀ᵐ x ∂μ, s x=1 → f x+g x=q)
    (horth : (∫ x, f x*s x ∂μ)*(∫ x, g x*s x ∂μ)=0) :
    ((∫ x, f x*s x ∂μ)/d=0 ∨ (∫ x, f x*s x ∂μ)/d=q) ∧
      ∀ᵐ x ∂μ, s x=1 → f x=(∫ y, f y*s y ∂μ)/d := by
  rcases mul_eq_zero.mp horth with hz | hz
  · refine ⟨Or.inl (by rw [hz,zero_div]),?_⟩
    filter_upwards [weighted_zero μ f s hf hs bf bs hz] with x hx
    intro hi
    rw [hx hi,hz,zero_div]
  · have hfq : ∀ᵐ x ∂μ, s x=1 → f x=q := by
      filter_upwards [hsum,weighted_zero μ g s hg hs bg bs hz] with x hx hy
      intro hi
      have hh := hx hi
      rw [hy hi,add_zero] at hh
      exact hh
    have hi : (∫ x, f x*s x ∂μ)=q*d := by
      calc
        _ = ∫ x, q*s x ∂μ := by
          apply integral_congr_ae
          filter_upwards [hfq] with x hx
          rcases bs x with h0 | h1
          · simp only [h0,mul_zero]
          · rw [hx h1]
        _ = _ := by rw [integral_const_mul,hm]
    have hratio : (∫ x, f x*s x ∂μ)/d=q := by rw [hi]; exact mul_div_cancel_right₀ q (ne_of_gt hd)
    refine ⟨Or.inr hratio,?_⟩
    filter_upwards [hfq] with x hx
    intro hi
    exact (hx hi).trans hratio.symm

/-- P vanishing inside the target class forces each A row to be constant there
whenever A+B already has a constant class-block value. -/
theorem class_row_constant (A B P : Ω × Ω → ℝ) (s t : Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hs : Measurable s) (ht : Measurable t)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x))
    (bt : ∀ x, t x=0 ∨ t x=1) (d q : ℝ) (hd : 0 < d) (hm : (∫ x, t x ∂μ)=d)
    (eP : ∀ᵐ p ∂μ.prod μ, P p=comp μ A B p+comp μ B A p)
    (hdiag : ∀ᵐ p ∂μ.prod μ, t p.1=1 → t p.2=1 → P p=0)
    (hQ : ∀ᵐ x ∂μ, s x=1 → ∀ᵐ y ∂μ, t y=1 → A (x,y)+B (x,y)=q) :
    ∀ᵐ x ∂μ, s x=1 →
      (act μ A t x/d=0 ∨ act μ A t x/d=q) ∧
      ∀ᵐ y ∂μ, t y=1 → A (x,y)=act μ A t x/d := by
  have bu (x : Ω) : 0 ≤ t x ∧ t x ≤ 1 := by rcases bt x with h | h <;> simp [h]
  have hz := TwoPairFiniteReduction.images_orthogonal μ A B P hA hB bA bB sA eP t ht bt hdiag
  have hfa := measurable_act μ A t hA ht
  have hfb := measurable_act μ B t hB ht
  have bfa := act_bounds μ A t hA ht bA bu
  have bfb := act_bounds μ B t hB ht bB bu
  have he := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (bfa x).1 (bfb x).1)
    (unit_integrable μ _ (hfa.mul hfb) (fun x => mul_unit (bfa x) (bfb x)))).mp hz
  filter_upwards [hQ,he] with x hx he
  intro hi
  exact split_row_constant μ (fun y => A (x,y)) (fun y => B (x,y)) t
    (by fun_prop) (by fun_prop) ht (fun y => bA (x,y)) (fun y => bB (x,y))
    bt d q hd hm (hx hi) he

lemma separated_class_constant (s t f g : Ω → ℝ)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (d q : ℝ) (hd : 0 < d) (ms : (∫ x, s x ∂μ)=d) (mt : (∫ x, t x ∂μ)=d)
    (he : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, s x=1 → t y=1 → f x=g y)
    (bf : ∀ᵐ x ∂μ, s x=1 → f x=0 ∨ f x=q) :
    ∃ b, (b=0 ∨ b=q) ∧
      (∀ᵐ x ∂μ, s x=1 → f x=b) ∧ (∀ᵐ y ∂μ, t y=1 → g y=b) := by
  obtain ⟨x,hsx,hx⟩ := positive_class_witness μ s bs d hd ms
    (fun x => (∀ᵐ y ∂μ, s x=1 → t y=1 → f x=g y) ∧ (s x=1 → f x=0 ∨ f x=q)) (he.and bf)
  have hg : ∀ᵐ y ∂μ, t y=1 → g y=f x := by
    filter_upwards [hx.1] with y hy
    intro hi
    exact (hy hsx hi).symm
  refine ⟨f x,hx.2 hsx,?_,hg⟩
  filter_upwards [he] with z hz
  intro hsz
  obtain ⟨y,hty,hy⟩ := positive_class_witness μ t bt d hd mt
    (fun y => (s z=1 → t y=1 → f z=g y) ∧ (t y=1 → g y=f x)) (hz.and hg)
  exact (hy.1 hsz hty).trans (hy.2 hty)

/-- Symmetry upgrades row-dependent class constants to one actual rectangle value. -/
theorem symmetric_block_constant (A : Ω × Ω → ℝ) (s t f g : Ω → ℝ)
    (hA : Measurable A) (hs : Measurable s) (ht : Measurable t)
    (hf : Measurable f) (hg : Measurable g)
    (sA : ∀ x y, A (x,y)=A (y,x))
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (d q : ℝ) (hd : 0 < d) (ms : (∫ x, s x ∂μ)=d) (mt : (∫ x, t x ∂μ)=d)
    (r1 : ∀ᵐ x ∂μ, s x=1 → (f x=0 ∨ f x=q) ∧ ∀ᵐ y ∂μ, t y=1 → A (x,y)=f x)
    (r2 : ∀ᵐ y ∂μ, t y=1 → ∀ᵐ x ∂μ, s x=1 → A (y,x)=g y) :
    ∃ b, (b=0 ∨ b=q) ∧ ∀ᵐ p ∂μ.prod μ, s p.1=1 → t p.2=1 → A p=b := by
  have rr : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, s x=1 → t y=1 → A (x,y)=g y := by
    filter_upwards [r2] with y hy
    by_cases hty : t y=1
    · filter_upwards [hy hty] with x hx
      intro hix _
      simpa only [sA x y] using hx hix
    · exact Filter.Eventually.of_forall (fun x _ hi => (hty hi).elim)
  have rr' : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, s x=1 → t y=1 → A (x,y)=g y := by
    apply (Measure.ae_ae_comm (p := fun x y => s x=1 → t y=1 → A (x,y)=g y) ?_).mpr rr
    exact (measurableSet_eq_fun (hs.comp measurable_fst) measurable_const).imp
      ((measurableSet_eq_fun (ht.comp measurable_snd) measurable_const).imp
        (measurableSet_eq_fun hA (hg.comp measurable_snd)))
  have he : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, s x=1 → t y=1 → f x=g y := by
    filter_upwards [r1,rr'] with x hx hy
    by_cases hix : s x=1
    · filter_upwards [(hx hix).2,hy] with y h1 h2
      intro _ hiy
      exact (h1 hiy).symm.trans (h2 hix hiy)
    · exact Filter.Eventually.of_forall (fun y hi _ => (hix hi).elim)
  have bf : ∀ᵐ x ∂μ, s x=1 → f x=0 ∨ f x=q := r1.mono (fun x hx hi => (hx hi).1)
  obtain ⟨b,hb,hfb,_⟩ := separated_class_constant μ s t f g bs bt d q hd ms mt he bf
  refine ⟨b,hb,?_⟩
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [r1,hfb] with x hx hy
    by_cases hix : s x=1
    · filter_upwards [(hx hix).2] with y hxy
      intro _ hiy
      exact (hxy hiy).trans (hy hix)
    · exact Filter.Eventually.of_forall (fun y hi _ => (hix hi).elim)
  · exact (measurableSet_eq_fun (hs.comp measurable_fst) measurable_const).imp
      ((measurableSet_eq_fun (ht.comp measurable_snd) measurable_const).imp
        (measurableSet_eq_fun hA measurable_const))

lemma class_value {ι : Type*} [DecidableEq ι] (s : ι → Ω → ℝ)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (i j : ι) (y : Ω) (hy : s j y=1) : s i y=if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl,hy]
  · rw [if_neg hij]
    have h := orth i j hij y
    simpa only [hy,mul_one] using h

lemma q_class_values {ι : Type*} [DecidableEq ι]
    (A B C D : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (c e : ι → ι)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (rC : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i))
    (rD : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => D (x,y)) =ᵐ[μ] s (e i))
    (hcomplete : ∀ᵐ p ∂μ.prod μ, 2*(A p+B p)+C p+D p=1) :
    ∀ i j, ∀ᵐ x ∂μ, s i x=1 → ∀ᵐ y ∂μ, s j y=1 →
      A (x,y)+B (x,y)=(1-(if c i=j then 1 else 0)-(if e i=j then 1 else 0))/2 := by
  intro i j
  filter_upwards [rC i,rD i,Measure.ae_ae_of_ae_prod hcomplete] with x hx hy hz
  intro hi
  filter_upwards [hx hi,hy hi,hz] with y hC hD hcomp
  intro hj
  have hc := class_value s orth (c i) j y hj
  have he := class_value s orth (e i) j y hj
  rw [hC,hD,hc,he] at hcomp
  linarith

lemma distinct_singleton_maps {ι : Type*} (c e τ : ι → ι)
    (he : Function.Involutive e) (hcomp : ∀ i, e (c i)=τ i) (hτ : ∀ i, τ i ≠ i) :
    ∀ i, c i ≠ e i := by
  intro i hi
  have hh := hcomp i
  rw [hi,he i] at hh
  exact hτ i hh.symm

lemma q_value_binary {ι : Type*} [DecidableEq ι] (c e : ι → ι)
    (hne : ∀ i, c i ≠ e i) (i j : ι) :
    ((1-(if c i=j then 1 else 0)-(if e i=j then 1 else 0))/2 : ℝ)=0 ∨
    ((1-(if c i=j then 1 else 0)-(if e i=j then 1 else 0))/2 : ℝ)=1/2 := by
  by_cases hc : c i=j <;> by_cases he : e i=j
  · exact (hne i (hc.trans he.symm)).elim
  · simp only [hc,he,↓reduceIte]; norm_num
  · simp only [hc,he,↓reduceIte]; norm_num
  · simp only [hc,he,↓reduceIte]; norm_num

/-- Actual singleton class reconstruction and H-diagonal zeros force an A table.
No A/B block constancy or flux orthogonality is assumed. -/
theorem actual_a_blocks {ι : Type*} [DecidableEq ι]
    (A B C D P : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (c e : ι → ι)
    (hA : Measurable A) (hB : Measurable B) (hs : ∀ i, Measurable (s i))
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (d : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (rC : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i))
    (rD : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => D (x,y)) =ᵐ[μ] s (e i))
    (hne : ∀ i, c i ≠ e i)
    (hcomplete : ∀ᵐ p ∂μ.prod μ, 2*(A p+B p)+C p+D p=1)
    (eP : ∀ᵐ p ∂μ.prod μ, P p=comp μ A B p+comp μ B A p)
    (hdiag : ∀ i, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s i p.2=1 → P p=0) :
    ∀ i j, ∃ b : ℝ, (b=0 ∨ b=1/2) ∧
      ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → A p=b := by
  have qrows := q_class_values μ A B C D s c e orth rC rD hcomplete
  intro i j
  let q : ℝ := (1-(if c i=j then 1 else 0)-(if e i=j then 1 else 0))/2
  let q' : ℝ := (1-(if c j=i then 1 else 0)-(if e j=i then 1 else 0))/2
  have r1 := class_row_constant μ A B P (s i) (s j) hA hB (hs i) (hs j) bA bB sA
    (bs j) d q hd (hm j) eP (hdiag j) (qrows i j)
  have r2 := class_row_constant μ A B P (s j) (s i) hA hB (hs j) (hs i) bA bB sA
    (bs i) d q' hd (hm i) eP (hdiag i) (qrows j i)
  obtain ⟨b,hb,hrect⟩ := symmetric_block_constant μ A (s i) (s j)
    (fun x => act μ A (s j) x/d) (fun x => act μ A (s i) x/d)
    hA (hs i) (hs j) ((measurable_act μ A (s j) hA (hs j)).div_const d)
    ((measurable_act μ A (s i) hA (hs i)).div_const d) sA (bs i) (bs j) d q hd
    (hm i) (hm j) r1 (r2.mono (fun x hx hi => (hx hi).2))
  refine ⟨b,?_,hrect⟩
  rcases hb with hb | hb
  · exact Or.inl hb
  · rcases q_value_binary c e hne i j with hq | hq
    · exact Or.inl (hb.trans hq)
    · exact Or.inr (hb.trans hq)

end TwoPairPrismABBlocks

end


-- Local module: TwoPairPrismTableEncoding
section
open scoped BigOperators
namespace TwoPairPrismTableEncoding
variable {I : Type*}
noncomputable def bit (a : I → I → ℝ) (i j : I) : Bool := by
  classical
  exact decide (a i j=(1:ℝ)/2)
lemma bit_true (a : I → I → ℝ) (i j : I) : bit a i j=true ↔ a i j=(1:ℝ)/2 := by
  classical
  simp only [bit,decide_eq_true_eq]
lemma bit_symmetric (a : I → I → ℝ) (hs : ∀ i j, a i j=a j i) :
    ∀ i j, bit a i j=bit a j i := by
  intro i j
  unfold bit
  rw [hs i j]
lemma row_card_two [Fintype I] (a : I → I → ℝ)
    (ha : ∀ i j, a i j=0 ∨ a i j=(1:ℝ)/2)
    (hr : ∀ i, ∑ j, a i j=1) :
    ∀ i, (Finset.univ.filter (fun j => bit a i j=true)).card=2 := by
  classical
  intro i
  have hval (j : I) : a i j=(if bit a i j=true then (1:ℝ) else 0)/2 := by
    by_cases h : bit a i j=true
    · rw [(bit_true a i j).mp h,if_pos h]
    · rw [if_neg h]
      rcases ha i j with hh | hh
      · simpa using hh
      · exact (h ((bit_true a i j).mpr hh)).elim
  have hh : (∑ j, a i j)=((Finset.univ.filter (fun j => bit a i j=true)).card:ℝ)/2 := by
    simp_rw [hval]
    rw [← Finset.sum_div,Finset.sum_boole]
  have hc : ((Finset.univ.filter (fun j => bit a i j=true)).card:ℝ)=2 := by
    rw [hr i] at hh
    linarith
  exact_mod_cast hc

lemma available_colors [DecidableEq I] (a b : I → I → ℝ) (c e : I → I)
    (ha : ∀ i j, a i j=0 ∨ a i j=(1:ℝ)/2)
    (hb : ∀ i j, b i j=0 ∨ b i j=(1:ℝ)/2)
    (hne : ∀ i, c i ≠ e i)
    (hsum : ∀ i j, a i j+b i j=(1-(if c i=j then 1 else 0)-(if e i=j then 1 else 0))/2) :
    (∀ i j, ¬ (bit a i j=true ∧ bit b i j=true)) ∧
    (∀ i j, (bit a i j=true ∨ bit b i j=true) ↔ j ≠ c i ∧ j ≠ e i) := by
  have bnA (i j : I) : 0 ≤ a i j := by rcases ha i j with h | h <;> rw [h] <;> norm_num
  have bnB (i j : I) : 0 ≤ b i j := by rcases hb i j with h | h <;> rw [h] <;> norm_num
  have hq (i j : I) : a i j+b i j ≤ (1:ℝ)/2 := by
    rw [hsum i j]
    rcases TwoPairPrismABBlocks.q_value_binary c e hne i j with h | h <;> rw [h] <;> norm_num
  have blocked (i j : I) (h : j=c i ∨ j=e i) : a i j+b i j=0 := by
    rw [hsum i j]
    rcases h with h | h
    · subst j
      have he : ¬ e i=c i := Ne.symm (hne i)
      rw [if_pos rfl,if_neg he]
      norm_num
    · subst j
      rw [if_neg (hne i),if_pos rfl]
      norm_num
  constructor
  · intro i j hh
    have h1 := (bit_true a i j).mp hh.1
    have h2 := (bit_true b i j).mp hh.2
    linarith [hq i j]
  · intro i j
    constructor
    · intro hh
      have hp : 0 < a i j+b i j := by
        rcases hh with hh | hh
        · rw [(bit_true a i j).mp hh]
          linarith [bnB i j]
        · rw [(bit_true b i j).mp hh]
          linarith [bnA i j]
      exact ⟨fun h => (ne_of_gt hp) (blocked i j (Or.inl h)),
        fun h => (ne_of_gt hp) (blocked i j (Or.inr h))⟩
    · intro hh
      have hsum' := hsum i j
      rw [if_neg (Ne.symm hh.1),if_neg (Ne.symm hh.2)] at hsum'
      rcases ha i j with hA | hA
      · rcases hb i j with hB | hB
        · norm_num [hA,hB] at hsum'
        · exact Or.inr ((bit_true b i j).mpr hB)
      · exact Or.inl ((bit_true a i j).mpr hA)

lemma mixed_edges (a b : I → I → ℝ) (H : I → I → Bool)
    (hz : ∀ i j k, H i j=false → a k i*b k j=0) :
    ∀ z x y, bit a z x=true → bit b z y=true → H x y=true := by
  intro z x y hx hy
  cases h : H x y with
  | true => rfl
  | false =>
    have hh := hz x y z h
    rw [(bit_true a z x).mp hx,(bit_true b z y).mp hy] at hh
    norm_num at hh
end TwoPairPrismTableEncoding
end


-- Local module: TwoPairPrismWitnessLift
section
open MeasureTheory
namespace TwoPairPrismWitnessLift
open FourColorKernels TwoPairPrismDescent TwoPairPrismCylinder TwoPairPrismTableEncoding
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma class_rectangle_one {I : Type*} (C : Ω × Ω → ℝ) (s : I → Ω → ℝ) (c : I → I)
    (hC : Measurable C) (hs : ∀ i, Measurable (s i))
    (hr : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i))
    (i j : I) (he : c i=j) :
    ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → C p=1 := by
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [hr i] with x hx
    by_cases hi : s i x=1
    · filter_upwards [hx hi] with y hy
      intro _ hj
      rw [hy,he,hj]
    · exact Filter.Eventually.of_forall (fun y h _ => (hi h).elim)
  · exact (measurableSet_eq_fun ((hs i).comp measurable_fst) measurable_const).imp
      ((measurableSet_eq_fun ((hs j).comp measurable_snd) measurable_const).imp
        (measurableSet_eq_fun hC measurable_const))

/-- An actual finite ACAD witness contradicts the original alternating-C4 zero. -/
theorem alternating_witness_contradiction {I : Type*}
    (A C D : Ω × Ω → ℝ) (s : I → Ω → ℝ) (a : I → I → ℝ) (c e : I → I)
    (hA : Measurable A) (hC : Measurable C) (hD : Measurable D)
    (hs : ∀ i, Measurable (s i))
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (hm : ∀ i, (∫ x, s i x ∂μ)=(1:ℝ)/6)
    (htab : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → A p=a i j)
    (rC : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i))
    (rD : ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => D (x,y)) =ᵐ[μ] s (e i))
    (hz : TwoPairCycleReduction.closing4 μ A C A D=0)
    (hw : ∃ x0 x1 x2 x3, bit a x0 x1=true ∧ c x1=x2 ∧ bit a x2 x3=true ∧ e x3=x0) : False := by
  obtain ⟨x0,x1,x2,x3,h01,h12,h23,h30⟩ := hw
  let W : Fin 4 → Ω × Ω → ℝ := ![A,C,A,D]
  let S : Fin 4 → Ω → ℝ := ![s x0,s x1,s x2,s x3]
  have hW : ∀ i, Measurable (W i) := by
    intro i
    fin_cases i <;> simp only [W,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption
  have bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1 := by
    intro i p
    fin_cases i <;> simp only [W,Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      first | exact bA p | exact bC p | exact bD p
  have bS : ∀ i x, S i x=0 ∨ S i x=1 := by
    intro i x
    fin_cases i <;> simp only [S,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> exact bs _ x
  have mS : ∀ i, (∫ x, S i x ∂μ)=(1:ℝ)/6 := by
    intro i
    fin_cases i <;> simp only [S,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> exact hm _
  have hrect0 : ∀ᵐ p ∂μ.prod μ, s x0 p.1=1 → s x1 p.2=1 → A p=(1:ℝ)/2 := by
    simpa only [(bit_true a x0 x1).mp h01] using htab x0 x1
  have hrect2 : ∀ᵐ p ∂μ.prod μ, s x2 p.1=1 → s x3 p.2=1 → A p=(1:ℝ)/2 := by
    simpa only [(bit_true a x2 x3).mp h23] using htab x2 x3
  have hn := four_class_cycle_nonzero μ W S hW bW bS (fun _ => (1:ℝ)/6)
    ![(1:ℝ)/2,1,1/2,1] (fun _ => by norm_num)
    (by intro i; fin_cases i <;> norm_num) mS hrect0
    (class_rectangle_one μ C s c hC hs rC x1 x2 h12) hrect2
    (class_rectangle_one μ D s e hD hs rD x3 x0 h30)
  apply hn
  exact (closing4_eq_cycle4 μ A C A D hA hC hA hD bA bC bA bD sA sD).symm.trans hz
end TwoPairPrismWitnessLift
end


-- Local module: TwoPairPrismTableConstraints
section
open MeasureTheory
open scoped BigOperators
namespace TwoPairPrismTableConstraints
open FourColorKernels TwoPairHalfSetOperator TwoPairPrismDescent
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma rectangle_witness (s t : Ω → ℝ)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1)
    (d : ℝ) (hd : 0 < d) (ms : (∫ x, s x ∂μ)=d) (mt : (∫ x, t x ∂μ)=d)
    (Good : Ω × Ω → Prop) (hg : ∀ᵐ p ∂μ.prod μ, Good p) :
    ∃ x y, s x=1 ∧ t y=1 ∧ Good (x,y) := by
  obtain ⟨x,hx,hgx⟩ := positive_class_witness μ s bs d hd ms
    (fun x => ∀ᵐ y ∂μ, Good (x,y)) (Measure.ae_ae_of_ae_prod hg)
  obtain ⟨y,hy,hgy⟩ := positive_class_witness μ t bt d hd mt (fun y => Good (x,y)) hgx
  exact ⟨x,y,hx,hy,hgy⟩

lemma symmetric_table {ι : Type*} (M : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (a : ι → ι → ℝ)
    (bs : ∀ i x, s i x=0 ∨ s i x=1) (d : ℝ) (hd : 0 < d)
    (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hsym : ∀ x y, M (x,y)=M (y,x))
    (htab : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → M p=a i j) :
    ∀ i j, a i j=a j i := by
  intro i j
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae (htab j i)
  obtain ⟨x,y,hx,hy,hp⟩ := rectangle_witness μ (s i) (s j) (bs i) (bs j) d hd (hm i) (hm j)
    (fun p => (s i p.1=1 → s j p.2=1 → M p=a i j) ∧
      (s j p.2=1 → s i p.1=1 → M (p.2,p.1)=a j i)) ((htab i j).and hswap)
  exact (hp.1 hx hy).symm.trans ((hsym x y).trans (hp.2 hy hx))

lemma table_row_mass {ι : Type*} [Fintype ι]
    (M : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (a : ι → ι → ℝ)
    (hs : ∀ i, Measurable (s i)) (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (hpart : ∀ x, ∑ i, s i x=1)
    (d r : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hr : ∀ᵐ x ∂μ, ∫ y, M (x,y) ∂μ=r)
    (htab : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → M p=a i j) :
    ∀ i, d*(∑ j, a i j)=r := by
  intro i
  have hall : ∀ᵐ x ∂μ, ∀ j, ∀ᵐ y ∂μ, s i x=1 → s j y=1 → M (x,y)=a i j := by
    apply ae_all_iff.mpr
    intro j
    exact Measure.ae_ae_of_ae_prod (htab i j)
  obtain ⟨x,hx,hgx⟩ := positive_class_witness μ (s i) (bs i) d hd (hm i)
    (fun x => (∫ y, M (x,y) ∂μ)=r ∧ ∀ j, ∀ᵐ y ∂μ, s i x=1 → s j y=1 → M (x,y)=a i j)
    (hr.and hall)
  have he : (fun y => M (x,y)) =ᵐ[μ] (fun y => ∑ j, a i j*s j y) := by
    have hh : ∀ᵐ y ∂μ, ∀ j, s i x=1 → s j y=1 → M (x,y)=a i j :=
      ae_all_iff.mpr hgx.2
    filter_upwards [hh] with y hy
    calc
      M (x,y) = M (x,y)*(∑ j, s j y) := by rw [hpart y,mul_one]
      _ = ∑ j, M (x,y)*s j y := Finset.mul_sum _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rcases bs j y with h0 | h1
        · simp only [h0,mul_zero]
        · rw [hy j hx h1]
  have bu (j : ι) (y : Ω) : 0 ≤ s j y ∧ s j y ≤ 1 := by
    rcases bs j y with h | h <;> simp [h]
  have hi (j : ι) : Integrable (fun y => a i j*s j y) μ :=
    (unit_integrable μ (s j) (hs j) (bu j)).const_mul (a i j)
  have ht : (∫ y, M (x,y) ∂μ)=d*(∑ j, a i j) := by
    rw [integral_congr_ae he,integral_finsetSum _ (fun j _ => hi j)]
    simp_rw [integral_const_mul,hm]
    rw [← Finset.sum_mul,mul_comm]
  exact ht.symm.trans hgx.1

lemma table_sum {ι : Type*} (A B : Ω × Ω → ℝ) (s : ι → Ω → ℝ)
    (a b q : ι → ι → ℝ) (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (d : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hA : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → A p=a i j)
    (hB : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → B p=b i j)
    (hQ : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → A p+B p=q i j) :
    ∀ i j, a i j+b i j=q i j := by
  intro i j
  obtain ⟨x,y,hx,hy,hp⟩ := rectangle_witness μ (s i) (s j) (bs i) (bs j) d hd (hm i) (hm j)
    (fun p => (s i p.1=1 → s j p.2=1 → A p=a i j) ∧
      (s i p.1=1 → s j p.2=1 → B p=b i j) ∧
      (s i p.1=1 → s j p.2=1 → A p+B p=q i j)) ((hA i j).and ((hB i j).and (hQ i j)))
  have hh := hp.2.2 hx hy
  rwa [hp.1 hx hy,hp.2.1 hx hy] at hh

lemma rectangle_path_product_zero (F G : Ω × Ω → ℝ) (s t u : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (bs : ∀ x, s x=0 ∨ s x=1) (bt : ∀ x, t x=0 ∨ t x=1) (bu : ∀ x, u x=0 ∨ u x=1)
    (d a b : ℝ) (hd : 0 < d)
    (ms : (∫ x, s x ∂μ)=d) (mt : (∫ x, t x ∂μ)=d) (mu : (∫ x, u x ∂μ)=d)
    (eF : ∀ᵐ p ∂μ.prod μ, s p.1=1 → u p.2=1 → F p=a)
    (eG : ∀ᵐ p ∂μ.prod μ, u p.1=1 → t p.2=1 → G p=b)
    (hz : ∀ᵐ p ∂μ.prod μ, s p.1=1 → t p.2=1 → comp μ F G p=0) : a*b=0 := by
  have frow := Measure.ae_ae_of_ae_prod eF
  have grow := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae eG)
  have zrow := Measure.ae_ae_of_ae_prod hz
  obtain ⟨x,hx,hgx⟩ := positive_class_witness μ s bs d hd ms
    (fun x => (∀ᵐ z ∂μ, s x=1 → u z=1 → F (x,z)=a) ∧
      (∀ᵐ y ∂μ, s x=1 → t y=1 → comp μ F G (x,y)=0)) (frow.and zrow)
  obtain ⟨y,hy,hgy⟩ := positive_class_witness μ t bt d hd mt
    (fun y => (s x=1 → t y=1 → comp μ F G (x,y)=0) ∧
      (∀ᵐ z ∂μ, u z=1 → t y=1 → G (z,y)=b)) (hgx.2.and grow)
  have hzero : ∀ᵐ z ∂μ, F (x,z)*G (z,y)=0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_nonneg (bF (x,z)).1 (bG (z,y)).1)
      (unit_integrable μ (fun z => F (x,z)*G (z,y))
        ((hF.comp (measurable_const.prodMk measurable_id)).mul
          (hG.comp (measurable_id.prodMk measurable_const)))
        (fun z => mul_unit (bF (x,z)) (bG (z,y))))).mp (hgy.1 hx hy)
  obtain ⟨z,hz,hgz⟩ := positive_class_witness μ u bu d hd mu
    (fun z => (s x=1 → u z=1 → F (x,z)=a) ∧
      (u z=1 → t y=1 → G (z,y)=b) ∧ F (x,z)*G (z,y)=0) (hgx.1.and (hgy.2.and hzero))
  have hh := hgz.2.2
  rwa [hgz.1 hx hz,hgz.2.1 hz hy] at hh

/-- Missing mixed-support blocks exclude every corresponding A/B table product. -/
theorem forbidden_mixed_table_products {ι : Type*}
    (A B P : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (a b : ι → ι → ℝ) (H : ι → ι → Bool)
    (hA : Measurable A) (hB : Measurable B)
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bs : ∀ i x, s i x=0 ∨ s i x=1) (d : ℝ) (hd : 0 < d)
    (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (ha : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → A p=a i j)
    (hb : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → B p=b i j)
    (asym : ∀ i j, a i j=a j i)
    (eP : ∀ᵐ p ∂μ.prod μ, P p=comp μ A B p+comp μ B A p)
    (hP : ∀ i j, H i j=false → ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → P p=0) :
    ∀ i j k, H i j=false → a k i*b k j=0 := by
  intro i j k hij
  have hz : ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → comp μ A B p=0 := by
    filter_upwards [eP,hP i j hij] with p hp hzero
    intro hi hj
    have hh := hzero hi hj
    have hn1 := (comp_bounds μ A B hA hB bA bB p).1
    have hn2 := (comp_bounds μ B A hB hA bB bA p).1
    linarith
  have h := rectangle_path_product_zero μ A B (s i) (s j) (s k) hA hB bA bB
    (bs i) (bs j) (bs k) d (a i k) (b k j) hd (hm i) (hm j) (hm k) (ha i k) (hb k j) hz
  rwa [asym i k] at h

end TwoPairPrismTableConstraints

end


-- Local module: TwoPairPrismFinite
section
namespace TwoPairPrismFinite
open TwoPairAntipodal

instance prismDecidable : DecidableRel prism := fun u v =>
  inferInstanceAs (Decidable ((u.1=v.1 ∧ u.2≠v.2) ∨ (u.1≠v.1 ∧ u.2=v.2)))

/- A genuine two-versus-two prism row has one selection in each available
pair, with opposite selected bits. This checks only the 64 six-bit rows. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 10000 in
lemma row_shape (r : Vertex → Bool) (q : Fin 3)
    (hforbid : ∀ b,r (q,b)=false)
    (hcard : (Finset.univ.filter (fun v => r v=true)).card=2)
    (hmixed : ∀ v w,r v=true → w.1≠q → r w=false → prism v w) :
    (∀ j b,j≠q → r (j,b+1)= !(r (j,b))) ∧
    (∀ j k,j≠q → k≠q → j≠k → r (j,0)≠r (k,0)) := by
  revert r q
  decide

noncomputable def bit (b : Bool) : ZMod 2 := if b then 0 else 1

lemma bit_ne_sum (a b : Bool) (h : a≠b) : bit a+bit b=1 := by
  cases a <;> cases b <;> simp_all [bit]

lemma bit_match (a : Bool) (b c : ZMod 2) :
    (if b=0 then (if c=0 then a else !a) else (if c=0 then !a else a))=true ↔
      b+c=bit a := by
  revert a b c
  unfold bit
  decide

/-- Flip in either coordinate, obtained from actual row shape and symmetry,
turns every available 2x2 block into a matching; shifts are derived. -/
lemma matching_block (A : Vertex → Vertex → Bool) (π : Fin 3 → Fin 3)
    (hinv : Function.Involutive π)
    (hs : ∀ u v,A u v=A v u)
    (hf : ∀ i b j c,j≠π i → A (i,b) (j,c+1)= !(A (i,b) (j,c)))
    (i j : Fin 3) (hij : j≠π i) (b c : ZMod 2) :
    A (i,b) (j,c)=true ↔ b+c=bit (A (i,0) (j,0)) := by
  have hji : i≠π j := by
    intro h
    apply hij
    rw [h,hinv j]
  have hright := hf i 0 j 0 hij
  have hleft := hf j 0 i 0 hji
  have hboth := hf i 1 j 0 hij
  simp only [zero_add] at hright hleft hboth
  rw [hs (j,0) (i,1),hs (j,0) (i,0)] at hleft
  have htable : A (i,b) (j,c)=
      (if b=0 then (if c=0 then A (i,0) (j,0) else !(A (i,0) (j,0)))
       else (if c=0 then !(A (i,0) (j,0)) else A (i,0) (j,0))) := by
    have hb : b=0 ∨ b=1 := by
      have h : ∀ t : ZMod 2,t=0 ∨ t=1 := by decide
      exact h b
    have hc : c=0 ∨ c=1 := by
      have h : ∀ t : ZMod 2,t=0 ∨ t=1 := by decide
      exact h c
    rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      rw [hb,hc] <;> simp only [zero_ne_one,one_ne_zero,↓reduceIte]
    · exact hright
    · exact hleft
    · rw [hboth,hleft]; simp
  rw [htable]
  exact bit_match _ b c

/- An involution on three points is the identity or one transposition. -/
set_option maxRecDepth 10000 in
lemma involution_three (π : Fin 3 → Fin 3) (hi : Function.Involutive π) :
    (∀ i,π i=i) ∨ ∃ i j k, i≠j ∧ i≠k ∧ j≠k ∧ π i=j ∧ π j=i ∧ π k=k := by
  revert π
  unfold Function.Involutive
  decide

lemma shift_sign_symmetric (A : Vertex → Vertex → Bool)
    (hs : ∀ u v,A u v=A v u) (i j : Fin 3) :
    bit (A (i,0) (j,0))=bit (A (j,0) (i,0)) := congrArg bit (hs _ _)

/-- Core finite argument after deriving row shapes. No matching profile is
assumed: `matching_block` derives it from the table. -/
lemma shifted_witness (A : Vertex → Vertex → Bool) (π : Fin 3 → Fin 3)
    (s : Fin 3 → ZMod 2) (hinv : Function.Involutive π)
    (hshift : ∀ i,s (π i)=s i)
    (hs : ∀ u v,A u v=A v u)
    (hshape : ∀ i b,
      (∀ j c,j≠π i → A (i,b) (j,c+1)= !(A (i,b) (j,c))) ∧
      (∀ j k,j≠π i → k≠π i → j≠k → A (i,b) (j,0)≠A (i,b) (k,0))) :
    ∃ i j e, π i=j ∧
      A (i,0) (i,e)=true ∧ A (j,e+s i) (j,s i+1)=true := by
  let a := fun i j => bit (A (i,0) (j,0))
  have ha : ∀ i j,a i j=a j i := shift_sign_symmetric A hs
  have hsum : ∀ i j k,j≠π i → k≠π i → j≠k → a i j+a i k=1 := by
    intro i j k hj hk hjk
    exact bit_ne_sum _ _ ((hshape i 0).2 j k hj hk hjk)
  rcases involution_three π hinv with hid | ⟨i,j,k,hij,hik,hjk,hpi,hpj,hpk⟩
  · have h0 : a 0 1+a 0 2=1 := hsum 0 1 2 (by rw [hid]; decide) (by rw [hid]; decide) (by decide)
    have h1 : a 0 1+a 1 2=1 := by
      rw [ha 0 1]
      exact hsum 1 0 2 (by rw [hid]; decide) (by rw [hid]; decide) (by decide)
    have h2 : a 0 2+a 1 2=1 := by
      rw [ha 0 2,ha 1 2]
      exact hsum 2 0 1 (by rw [hid]; decide) (by rw [hid]; decide) (by decide)
    exact (TwoPairPrismBits.identity_shifts_impossible _ _ _ h0 h1 h2).elim
  · have hi : a i i+a i k=1 := hsum i i k (by simpa only [hpi] using hij)
      (by simpa only [hpi] using Ne.symm hjk) hik
    have hj : a j j+a j k=1 := hsum j j k (by simpa only [hpj] using Ne.symm hij)
      (by simpa only [hpj] using Ne.symm hik) hjk
    have hk : a i k+a j k=1 := by
      rw [ha i k,ha j k]
      exact hsum k i j (by simpa only [hpk] using hik) (by simpa only [hpk] using hjk) hij
    have he : a i i+a j j=1 := TwoPairPrismBits.own_shifts_opposite _ _ _ _ hi hj hk
    refine ⟨i,j,a i i,hpi,?_,?_⟩
    · apply (matching_block A π hinv hs (fun i b => (hshape i b).1) i i
        (by simpa only [hpi] using hij) 0 (a i i)).mpr
      simp only [zero_add]
      rfl
    · apply (matching_block A π hinv hs (fun i b => (hshape i b).1) j j
        (by simpa only [hpj] using Ne.symm hij) (a i i+s i) (s i+1)).mpr
      change (a i i+s i)+(s i+1)=a j j
      have hbit : ∀ e1 e2 t : ZMod 2,e1+e2=1 → (e1+t)+(t+1)=e2 := by decide
      exact hbit _ _ _ he

def flip (v : Vertex) : Vertex := (v.1,v.2+1)

lemma bit_two (a b : ZMod 2) : a=b ∨ a=b+1 := by
  revert a b
  decide

/-- Exact finite interface for analytic descent: two original singleton
involutions, actual A/B tables, and the mixed-path support restriction. -/
theorem actual_prism_witness (A B : Vertex → Vertex → Bool) (c e : Vertex → Vertex)
    (hc : Function.Involutive c) (he : Function.Involutive e)
    (hce : ∀ u,c (e u)=flip u) (hec : ∀ u,e (c u)=flip u)
    (hAs : ∀ u v,A u v=A v u)
    (hcard : ∀ u,(Finset.univ.filter (fun v => A u v=true)).card=2)
    (hcover : ∀ u v,(A u v=true ∨ B u v=true) ↔ v≠c u ∧ v≠e u)
    (hmixed : ∀ u v w,A u v=true → B u w=true → prism v w) :
    ∃ x0 x1 x2 x3,A x0 x1=true ∧ c x1=x2 ∧ A x2 x3=true ∧ e x3=x0 := by
  let π : Fin 3 → Fin 3 := fun i => (c (i,0)).1
  let s : Fin 3 → ZMod 2 := fun i => (c (i,0)).2
  have hcomm : ∀ u,c (flip u)=flip (c u) := by
    intro u
    rw [← hec u,hce]
  have hcf : ∀ i b,c (i,b)=(π i,b+s i) := by
    intro i b
    rcases bit_two b 0 with hb | hb
    · subst b
      simp only [zero_add]
      rfl
    · simp only [zero_add] at hb
      subst b
      have hh := hcomm (i,0)
      simpa only [flip,zero_add,add_comm] using hh
  have hef : ∀ i b,e (i,b)=(π i,b+s i+1) := by
    intro i b
    have hh := hec (c (i,b))
    rw [hc] at hh
    rw [hh,hcf]
    rfl
  have hpi : Function.Involutive π := by
    intro i
    have hh := hc (i,0)
    rw [hcf,hcf] at hh
    exact congrArg Prod.fst hh
  have hsi : ∀ i,s (π i)=s i := by
    intro i
    have hh := hc (i,0)
    rw [hcf,hcf] at hh
    have ht := congrArg Prod.snd hh
    change 0+s i+s (π i)=0 at ht
    have hbit : ∀ a b : ZMod 2,0+a+b=0 → b=a := by decide
    exact hbit _ _ ht
  have hshape : ∀ i b,
      (∀ j t,j≠π i → A (i,b) (j,t+1)= !(A (i,b) (j,t))) ∧
      (∀ j k,j≠π i → k≠π i → j≠k → A (i,b) (j,0)≠A (i,b) (k,0)) := by
    intro i b
    refine row_shape (A (i,b)) (π i) ?_ (hcard (i,b)) ?_
    · intro t
      cases hv : A (i,b) (π i,t)
      · rfl
      · have hav := (hcover (i,b) (π i,t)).mp (Or.inl hv)
        rcases bit_two t (b+s i) with ht | ht
        · exact False.elim (hav.1 (by rw [hcf,ht]))
        · exact False.elim (hav.2 (by rw [hef,ht]))
    · intro v w hv hw hwa
      have hwc : w≠c (i,b) := by
        intro h
        have hh := congrArg Prod.fst h
        rw [hcf] at hh
        exact hw hh
      have hwe : w≠e (i,b) := by
        intro h
        have hh := congrArg Prod.fst h
        rw [hef] at hh
        exact hw hh
      rcases (hcover (i,b) w).mpr ⟨hwc,hwe⟩ with ha | hb
      · rw [hwa] at ha
        cases ha
      · exact hmixed (i,b) v w hv hb
  obtain ⟨i,j,t,hij,hA1,hA2⟩ := shifted_witness A π s hpi hsi hAs hshape
  refine ⟨(i,0),(i,t),c (i,t),e (i,0),hA1,rfl,?_,he (i,0)⟩
  rw [hcf,hef,hij,zero_add]
  exact hA2

end TwoPairPrismFinite

end


-- Local module: TwoPairPrismAEPartition
section
open MeasureTheory
open scoped BigOperators
namespace TwoPairPrismAEPartition
open FourColorKernels TwoPairHalfSetOperator TwoPairPrismDescent
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
theorem rows_are_whole_classes_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Ω × Ω → ℝ) (s : ι → Ω → ℝ)
    (hC : Measurable C) (hs : ∀ i, Measurable (s i))
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (bs : ∀ i x, 0 ≤ s i x ∧ s i x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (d : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hpartition : ∀ᵐ x ∂μ, ∑ i, s i x=1)
    (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (hconf : ∀ i j, i ≠ j → ∀ᵐ p ∂μ.prod μ,
      s i p.1*comp μ C C p*s j p.2=0) :
    ∀ᵐ x ∂μ, ∃ i, (fun y => C (x,y)) =ᵐ[μ] s i := by
  have hflux : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → act μ C (s i) x*act μ C (s j) x=0 := by
    apply (ae_all_iff).mpr
    intro i
    apply (ae_all_iff).mpr
    intro j
    by_cases hij : i=j
    · exact Filter.Eventually.of_forall (fun x hn => (hn hij).elim)
    · exact (cross_flux_zero μ C (s i) (s j) hC (hs i) (hs j) bC (bs i) (bs j) sC (hconf i j hij)).mono
        (fun x hx _ => hx)
  filter_upwards [hr,hflux] with x hx hpair
  have hsum : ∑ i, act μ C (s i) x=d := by
    unfold act
    rw [← integral_finsetSum _ (fun i _ =>
      unit_integrable μ _ (by fun_prop) (fun y => mul_unit (bC (x,y)) (bs i y)))]
    calc
      _ = ∫ y, C (x,y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hpartition] with y hy
        rw [← Finset.mul_sum,hy,mul_one]
      _ = d := hx
  have bn (i : ι) : 0 ≤ act μ C (s i) x := (act_bounds μ C (s i) hC (hs i) bC (bs i) x).1
  have hex : ∃ i, 0 < act μ C (s i) x := by
    by_contra hn
    have hz : ∀ i, act μ C (s i) x=0 := by
      intro i
      have hni : ¬ 0 < act μ C (s i) x := fun hi => hn ⟨i,hi⟩
      linarith [bn i]
    simp only [hz,Finset.sum_const_zero] at hsum
    linarith
  obtain ⟨i,hi⟩ := hex
  have hothers (j : ι) (hji : j ≠ i) : act μ C (s j) x=0 :=
    (mul_eq_zero.mp (hpair i j (Ne.symm hji))).resolve_left (ne_of_gt hi)
  have hiMass : act μ C (s i) x=d := by
    rw [Finset.sum_eq_single i (fun j _ hji => hothers j hji) (by simp)] at hsum
    exact hsum
  refine ⟨i,saturated_row μ (fun y => C (x,y)) (s i) (by fun_prop) (hs i)
    (fun y => bC (x,y)) (bs i) d hx (hm i) hiMass⟩

theorem square_confined_involution_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Ω × Ω → ℝ) (s : ι → Ω → ℝ)
    (hC : Measurable C) (hs : ∀ i, Measurable (s i))
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (hpartition : ∀ᵐ x ∂μ, ∑ i, s i x=1)
    (d : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (hconf : ∀ i j, i ≠ j → ∀ᵐ p ∂μ.prod μ,
      s i p.1*comp μ C C p*s j p.2=0) :
    ∃ c : ι → ι, Function.Involutive c ∧
      ∀ i, ∀ᵐ x ∂μ, s i x=1 → (fun y => C (x,y)) =ᵐ[μ] s (c i) := by
  have bu (i : ι) (x : Ω) : 0 ≤ s i x ∧ s i x ≤ 1 := by
    rcases bs i x with hx | hx <;> rw [hx] <;> norm_num
  exact reconstruct_involution μ C s hC hs sC bs orth d hd hm
    (rows_are_whole_classes_ae μ C s hC hs bC bu sC d hd hm hpartition hr hconf)

lemma table_row_mass_ae {ι : Type*} [Fintype ι]
    (M : Ω × Ω → ℝ) (s : ι → Ω → ℝ) (a : ι → ι → ℝ)
    (hs : ∀ i, Measurable (s i)) (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (hpart : ∀ᵐ x ∂μ, ∑ i, s i x=1)
    (d r : ℝ) (hd : 0 < d) (hm : ∀ i, (∫ x, s i x ∂μ)=d)
    (hr : ∀ᵐ x ∂μ, ∫ y, M (x,y) ∂μ=r)
    (htab : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → M p=a i j) :
    ∀ i, d*(∑ j, a i j)=r := by
  intro i
  have hall : ∀ᵐ x ∂μ, ∀ j, ∀ᵐ y ∂μ, s i x=1 → s j y=1 → M (x,y)=a i j := by
    apply ae_all_iff.mpr
    intro j
    exact Measure.ae_ae_of_ae_prod (htab i j)
  obtain ⟨x,hx,hgx⟩ := positive_class_witness μ (s i) (bs i) d hd (hm i)
    (fun x => (∫ y, M (x,y) ∂μ)=r ∧ ∀ j, ∀ᵐ y ∂μ, s i x=1 → s j y=1 → M (x,y)=a i j)
    (hr.and hall)
  have he : (fun y => M (x,y)) =ᵐ[μ] (fun y => ∑ j, a i j*s j y) := by
    have hh : ∀ᵐ y ∂μ, ∀ j, s i x=1 → s j y=1 → M (x,y)=a i j :=
      ae_all_iff.mpr hgx.2
    filter_upwards [hh,hpart] with y hy hcover
    calc
      M (x,y) = M (x,y)*(∑ j, s j y) := by rw [hcover,mul_one]
      _ = ∑ j, M (x,y)*s j y := Finset.mul_sum _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rcases bs j y with h0 | h1
        · simp only [h0,mul_zero]
        · rw [hy j hx h1]
  have bu (j : ι) (y : Ω) : 0 ≤ s j y ∧ s j y ≤ 1 := by
    rcases bs j y with h | h <;> simp [h]
  have hi (j : ι) : Integrable (fun y => a i j*s j y) μ :=
    (unit_integrable μ (s j) (hs j) (bu j)).const_mul (a i j)
  have ht : (∫ y, M (x,y) ∂μ)=d*(∑ j, a i j) := by
    rw [integral_congr_ae he,integral_finsetSum _ (fun j _ => hi j)]
    simp_rw [integral_const_mul,hm]
    rw [← Finset.sum_mul,mul_comm]
  exact ht.symm.trans hgx.1


end TwoPairPrismAEPartition
end


-- Local module: TwoPairPrismAssembly
section
open MeasureTheory
open scoped BigOperators
namespace TwoPairPrismAssembly
open TwoPairPrismAEPartition
open FourColorKernels TwoPairPrismDescent TwoPairPrismKernelClassification TwoPairPrismABBlocks
open TwoPairPrismTableConstraints TwoPairPrismTableEncoding TwoPairPrismWitnessLift TwoPairAntipodal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The actual six equal-class prism branch is impossible. All finite table
constraints are derived from measurable kernel hypotheses. -/
theorem prism_impossible
    (A B C D P : Ω × Ω → ℝ) (s : Vertex → Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (hs : ∀ i, Measurable (s i))
    (bA : ∀ p, 0 ≤ A p ∧ A p ≤ 1) (bB : ∀ p, 0 ≤ B p ∧ B p ≤ 1)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (sA : ∀ x y, A (x,y)=A (y,x)) (sB : ∀ x y, B (x,y)=B (y,x))
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (bs : ∀ i x, s i x=0 ∨ s i x=1)
    (orth : ∀ i j, i ≠ j → ∀ x, s i x*s j x=0)
    (hpart : ∀ᵐ x ∂μ, ∑ i, s i x=1)
    (hm : ∀ i, (∫ x, s i x ∂μ)=(1:ℝ)/6)
    (rA : ∀ᵐ x ∂μ, ∫ y, A (x,y) ∂μ=(1:ℝ)/6)
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6)
    (hCC : ∀ i j, i ≠ j → ∀ᵐ p ∂μ.prod μ, s i p.1*comp μ C C p*s j p.2=0)
    (hDD : ∀ i j, i ≠ j → ∀ᵐ p ∂μ.prod μ, s i p.1*comp μ D D p*s j p.2=0)
    (hL : ∀ i j, j ≠ TwoPairPrismFinite.flip i → ∀ᵐ p ∂μ.prod μ,
      s i p.1*(comp μ C D p+comp μ D C p)*s j p.2=0)
    (hcomplete : ∀ᵐ p ∂μ.prod μ, 2*(A p+B p)+C p+D p=1)
    (eP : ∀ᵐ p ∂μ.prod μ, P p=comp μ A B p+comp μ B A p)
    (hP : ∀ i j, ¬ prism i j → ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → P p=0)
    (hz : TwoPairCycleReduction.closing4 μ A C A D=0) : False := by
  classical
  obtain ⟨c,hc,rc⟩ := square_confined_involution_ae μ C s hC hs bC sC bs orth hpart
    (1/6) (by norm_num) hm rC hCC
  obtain ⟨e,he,re⟩ := square_confined_involution_ae μ D s hD hs bD sD bs orth hpart
    (1/6) (by norm_num) hm rD hDD
  obtain ⟨hec,hce⟩ := composition_maps_antipodal μ C D s c e TwoPairPrismFinite.flip hC hD hs bC bD sC sD bs
    (1/6) (by norm_num) hm rc re hL
  have hflip : ∀ i : Vertex, TwoPairPrismFinite.flip i ≠ i := by
    intro i
    rcases i with ⟨i,b⟩
    intro h
    have hh : b + 1 = b := congrArg Prod.snd h
    have hh1 : (1 : ZMod 2) = 0 := add_left_cancel (hh.trans (add_zero b).symm)
    norm_num at hh1
  have hne := distinct_singleton_maps c e TwoPairPrismFinite.flip he hec hflip
  have hdiag : ∀ i, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s i p.2=1 → P p=0 := by
    intro i
    exact hP i i (by simp [prism])
  have aexist := actual_a_blocks μ A B C D P s c e hA hB hs bA bB sA bs orth
    (1/6) (by norm_num) hm rc re hne hcomplete eP hdiag
  have hcomplete' : ∀ᵐ p ∂μ.prod μ, 2*(B p+A p)+C p+D p=1 := by
    simpa only [add_comm] using hcomplete
  have eP' : ∀ᵐ p ∂μ.prod μ, P p=comp μ B A p+comp μ A B p := by
    simpa only [add_comm] using eP
  have bexist := actual_a_blocks μ B A C D P s c e hB hA hs bB bA sB bs orth
    (1/6) (by norm_num) hm rc re hne hcomplete' eP' hdiag
  choose a ha hta using aexist
  choose b hb htb using bexist
  have asym := symmetric_table μ A s a bs (1/6) (by norm_num) hm sA hta
  have mass := table_row_mass_ae μ A s a hs bs hpart (1/6) (1/6) (by norm_num) hm rA hta
  have ar : ∀ i, ∑ j, a i j=1 := by
    intro i
    have hh := mass i
    linarith
  let q : Vertex → Vertex → ℝ := fun i j => (1-(if c i=j then 1 else 0)-(if e i=j then 1 else 0))/2
  have qrows := q_class_values μ A B C D s c e orth rc re hcomplete
  have hq : ∀ i j, ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → A p+B p=q i j := by
    intro i j
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [qrows i j] with x hx
      by_cases hi : s i x=1
      · filter_upwards [hx hi] with y hy
        intro _ hj
        exact hy hj
      · exact Filter.Eventually.of_forall (fun y h _ => (hi h).elim)
    · exact (measurableSet_eq_fun ((hs i).comp measurable_fst) measurable_const).imp
        ((measurableSet_eq_fun ((hs j).comp measurable_snd) measurable_const).imp
          (measurableSet_eq_fun (hA.add hB) measurable_const))
  have hsum := table_sum μ A B s a b q bs (1/6) (by norm_num) hm hta htb hq
  have hboolcover := (available_colors a b c e ha hb hne hsum).2
  let H : Vertex → Vertex → Bool := fun i j => decide (prism i j)
  have hP' : ∀ i j, H i j=false → ∀ᵐ p ∂μ.prod μ, s i p.1=1 → s j p.2=1 → P p=0 := by
    intro i j hij
    exact hP i j (of_decide_eq_false hij)
  have hprod := forbidden_mixed_table_products μ A B P s a b H hA hB bA bB bs
    (1/6) (by norm_num) hm hta htb asym eP hP'
  have hmix : ∀ z x y, bit a z x=true → bit b z y=true → prism x y := by
    intro z x y hx hy
    exact of_decide_eq_true (mixed_edges a b H hprod z x y hx hy)
  have hw := TwoPairPrismFinite.actual_prism_witness (bit a) (bit b) c e hc he hce hec
    (bit_symmetric a asym) (row_card_two a ha ar) hboolcover hmix
  exact alternating_witness_contradiction μ A C D s a c e hA hC hD hs bA bC bD sA sD
    bs hm hta rc re hz hw
end TwoPairPrismAssembly
end


-- Local module: TwoPairPrismConfinement
section
open MeasureTheory
namespace TwoPairPrismConfinement
open FourColorKernels TwoPairHalfSetOperator TwoPairFiniteReduction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The confinement used in finite reduction is independent of any chosen partition. -/
theorem square_support_confinement
    (C D P L : Ω × Ω → ℝ)
    (hC : Measurable C) (hD : Measurable D) (hP : Measurable P) (hL : Measurable L)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bD : ∀ p, 0 ≤ D p ∧ D p ≤ 1)
    (bP : ∀ p, 0 ≤ P p ∧ P p ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (sD : ∀ x y, D (x,y)=D (y,x))
    (sP : ∀ x y, P (x,y)=P (y,x))
    (rC : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/6)
    (rD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=(1:ℝ)/6)
    (eL : ∀ᵐ p ∂μ.prod μ, L p=comp μ C D p+comp μ D C p)
    (hzP : ∀ᵐ p ∂μ.prod μ, comp μ P P p*L p=0)
    (hhalf : ∀ᵐ x ∂μ, μ {y | 0 < P (x,y)}=(1:ENNReal)/2) :
    ∀ᵐ p ∂μ.prod μ, 0 < comp μ C C p →
      (fun z => supportKernel P (p.1,z)) =ᵐ[μ] (fun z => supportKernel P (p.2,z)) := by
  have hind := (TwoPairHalfSupportBridge.independence_and_disjointness μ P L hP hL bP sP hzP).1
  have hH := supportKernel_measurable P hP
  have bH := supportKernel_binary P
  have sH := supportKernel_symm P sP
  have heigen : ∀ᵐ z ∂μ, ∀ᵐ x ∂μ,
      act μ (comp μ C C) (fun y => supportKernel P (z,y)) x=(1:ℝ)/36*supportKernel P (z,x) := by
    filter_upwards [hhalf,hind] with z hz hzi
    let S : Set Ω := {y | 0 < P (z,y)}
    have hS : MeasurableSet S := measurableSet_lt measurable_const
      (hP.comp (measurable_const.prodMk measurable_id))
    have hzind : ∀ᵐ p ∂μ.prod μ, oneSet S p.1=1 → oneSet S p.2=1 → L p=0 := by
      filter_upwards [hzi] with p hp
      intro hx hy
      have hx' : 0 < P (z,p.1) := by by_contra hn; simp [oneSet,S,hn] at hx
      have hy' : 0 < P (z,p.2) := by by_contra hn; simp [oneSet,S,hn] at hy
      exact hp hx' hy'
    have him := images_orthogonal μ C D L hC hD bC bD sC eL
      (oneSet S) (oneSet_measurable S hS) (oneSet_binary S) hzind
    have hsquare := half_set_square_preservation μ C D hC hD bC bD sC sD
      (1/6) (by norm_num) rC rD S hS hz him
    have he : oneSet S=(fun y => supportKernel P (z,y)) := by
      funext y
      by_cases hy : 0 < P (z,y) <;> simp [oneSet,supportKernel,S,hy]
    filter_upwards [hsquare] with x hx
    simpa only [he,show ((1:ℝ)/6)^2=1/36 by norm_num] using hx
  have rK : ∀ᵐ x ∂μ, ∫ y, comp μ C C (x,y) ∂μ=(1:ℝ)/36 := by
    simpa only [show ((1:ℝ)/6)*((1:ℝ)/6)=1/36 by norm_num] using
      comp_row μ C C hC hC bC bC (1/6) (1/6) rC rC
  exact TwoPairRowConfinement.row_confinement μ (comp μ C C) (supportKernel P)
    (measurable_comp μ C C hC hC) hH (comp_bounds μ C C hC hC bC bC) bH sH
    (1/36) rK heigen
end TwoPairPrismConfinement
end


-- Local module: TwoPairPrismFaithfulness
section
open MeasureTheory
namespace TwoPairPrismFaithfulness
open TwoPairAntipodal TwoPairPrismFinite TwoPairPrismDescent
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma prism_rows_injective (u v : Vertex) (h : ∀ w,prism u w ↔ prism v w) : u=v := by
  revert u v
  decide

lemma prism_rows_complement (u v : Vertex) (h : ∀ w,prism u w ↔ ¬prism v w) : v=flip u := by
  revert u v
  decide

def value (u v : Vertex) : ℝ := if prism u v then 1 else 0

lemma positive_test_equal (s f g : Ω → ℝ) (bs : ∀ z,s z=0 ∨ s z=1)
    (d : ℝ) (hd : 0<d) (hm : (∫ z,s z ∂μ)=d) (a b : ℝ)
    (hf : ∀ᵐ z ∂μ,s z=1 → f z=a) (hg : ∀ᵐ z ∂μ,s z=1 → g z=b)
    (he : f =ᵐ[μ] g) : a=b := by
  obtain ⟨z,hz,hfz,hgz,hez⟩ := positive_class_witness μ s bs d hd hm _ (hf.and (hg.and he))
  exact (hfz hz).symm.trans (hez.trans (hgz hz))

lemma positive_test_complement (s f g : Ω → ℝ) (bs : ∀ z,s z=0 ∨ s z=1)
    (d : ℝ) (hd : 0<d) (hm : (∫ z,s z ∂μ)=d) (a b : ℝ)
    (hf : ∀ᵐ z ∂μ,s z=1 → f z=a) (hg : ∀ᵐ z ∂μ,s z=1 → g z=b)
    (he : f =ᵐ[μ] (fun z => 1-g z)) : a=1-b := by
  obtain ⟨z,hz,hfz,hgz,hez⟩ := positive_class_witness μ s bs d hd hm _ (hf.and (hg.and he))
  change f z=1-g z at hez
  rw [hfz hz,hgz hz] at hez
  exact hez

/-- The prism table is faithful to actual a.e. rows. Positive test classes
eliminate any equality/complementarity not present in its six finite rows. -/
theorem actual_rows_faithful (H : Ω × Ω → ℝ) (s : Vertex → Ω → ℝ)
    (bs : ∀ i z,s i z=0 ∨ s i z=1) (d : ℝ) (hd : 0<d)
    (hm : ∀ i,(∫ z,s i z ∂μ)=d)
    (ht : ∀ i j,∀ᵐ p ∂μ.prod μ,s i p.1=1 → s j p.2=1 → H p=value i j) :
    ∀ i j,∀ᵐ x ∂μ,∀ᵐ y ∂μ,s i x=1 → s j y=1 →
      (((fun z => H (x,z)) =ᵐ[μ] (fun z => H (y,z))) → i=j) ∧
      (((fun z => H (x,z)) =ᵐ[μ] (fun z => 1-H (y,z))) → j=flip i) := by
  intro i j
  have hxall : ∀ᵐ x ∂μ,∀ k,∀ᵐ z ∂μ,s i x=1 → s k z=1 → H (x,z)=value i k :=
    ae_all_iff.mpr (fun k => Measure.ae_ae_of_ae_prod (ht i k))
  have hyall : ∀ᵐ y ∂μ,∀ k,∀ᵐ z ∂μ,s j y=1 → s k z=1 → H (y,z)=value j k :=
    ae_all_iff.mpr (fun k => Measure.ae_ae_of_ae_prod (ht j k))
  filter_upwards [hxall] with x hx
  filter_upwards [hyall] with y hy
  intro hix hjy
  have hxi (k) : ∀ᵐ z ∂μ,s k z=1 → H (x,z)=value i k := (hx k).mono (fun z hz => hz hix)
  have hyj (k) : ∀ᵐ z ∂μ,s k z=1 → H (y,z)=value j k := (hy k).mono (fun z hz => hz hjy)
  constructor
  · intro he
    apply prism_rows_injective
    intro k
    have hh := positive_test_equal μ (s k) _ _ (bs k) d hd (hm k) _ _ (hxi k) (hyj k) he
    by_cases hi : prism i k <;> by_cases hj : prism j k <;> simp [value,hi,hj] at hh ⊢
  · intro he
    apply prism_rows_complement
    intro k
    have hh := positive_test_complement μ (s k) _ _ (bs k) d hd (hm k) _ _ (hxi k) (hyj k) he
    by_cases hi : prism i k <;> by_cases hj : prism j k <;> simp [value,hi,hj] at hh ⊢

/-- Convert the restricted-product output of support reconstruction to the
indicator conditional table used by the analytic prism descent. -/
lemma set_blocks_to_indicator_table (H : Ω × Ω → ℝ) (hH : Measurable H)
    (X : Vertex → Set Ω) (hX : ∀ i,MeasurableSet (X i))
    (hr : ∀ i j,H =ᵐ[(μ.restrict (X i)).prod (μ.restrict (X j))]
      (fun _ => value i j)) :
    ∀ i j,∀ᵐ p ∂μ.prod μ,
      TwoPairHalfSetOperator.oneSet (X i) p.1=1 →
      TwoPairHalfSetOperator.oneSet (X j) p.2=1 → H p=value i j := by
  intro i j
  have hout : ∀ᵐ x ∂μ,x∈X i → ∀ᵐ y ∂μ.restrict (X j),H (x,y)=value i j :=
    (ae_restrict_iff' (hX i)).mp (Measure.ae_ae_of_ae_prod (hr i j))
  have hh : ∀ᵐ p ∂μ.prod μ,p.1∈X i → p.2∈X j → H p=value i j := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [hout] with x hx
      by_cases hxi : x∈X i
      · filter_upwards [(ae_restrict_iff' (hX j)).mp (hx hxi)] with y hy
        exact fun _ => hy
      · exact Filter.Eventually.of_forall (fun y hi _ => (hxi hi).elim)
    · exact ((hX i).preimage measurable_fst).imp
        (((hX j).preimage measurable_snd).imp (measurableSet_eq_fun hH measurable_const))
  filter_upwards [hh] with p hp
  intro hi hj
  have hxi : p.1∈X i := by
    by_contra hn
    simp [TwoPairHalfSetOperator.oneSet,hn] at hi
  have hxj : p.2∈X j := by
    by_contra hn
    simp [TwoPairHalfSetOperator.oneSet,hn] at hj
  exact hp hxi hxj

end TwoPairPrismFaithfulness

end


-- Local module: TwoPairNormalizedPrism
section
open MeasureTheory
open scoped BigOperators
namespace TwoPairNormalizedPrism
open FourColorKernels TwoPairHalfSetOperator TwoPairFiniteReduction
open TwoPairStructuralReduction TwoPairAntipodal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The actual prism alternative is impossible for the normalized two-pair kernels. -/
theorem normalized_prism_impossible (W : Fin 4 → Ω × Ω → ℝ)
    (hm : ∀ i,Measurable (W i)) (hb : ∀ i p,0≤W i p ∧ W i p≤1)
    (hs : ∀ i x y,W i (x,y)=W i (y,x))
    (hr : ∀ i,∀ᵐ x ∂μ,∫ y,W i (x,y) ∂μ=(1/6:ℝ))
    (hpart : ∀ p,2*W 0 p+2*W 1 p+W 2 p+W 3 p=1)
    (facts : NormalizedFacts μ W)
    (G : Set Ω) (hG : ∀ᵐ x ∂μ,x∈G)
    (X : Vertex → Set Ω)
    (hX : ∀ i,MeasurableSet (X i) ∧ μ.real (X i)=(1/6:ℝ))
    (hdis : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hcover : (⋃ i,X i)=G)
    (htable : ∀ i j,supportKernel (mixed μ W) =ᵐ[(μ.restrict (X i)).prod (μ.restrict (X j))]
      (fun _ => if prism i j then (1:ℝ) else 0)) : False := by
  classical
  let P := mixed μ W
  let L := singletonMixed μ W
  let H := supportKernel P
  let s := fun i => oneSet (X i)
  have hP : Measurable P := (measurable_comp μ _ _ (hm 0) (hm 1)).add
    (measurable_comp μ _ _ (hm 1) (hm 0))
  have hL : Measurable L := (measurable_comp μ _ _ (hm 2) (hm 3)).add
    (measurable_comp μ _ _ (hm 3) (hm 2))
  have sP : ∀ x y,P (x,y)=P (y,x) := mixed_symmetry μ _ _ (hs 0) (hs 1)
  have hH : Measurable H := supportKernel_measurable P hP
  have hsm : ∀ i,Measurable (s i) := fun i => oneSet_measurable _ (hX i).1
  have bsm : ∀ i x,s i x=0 ∨ s i x=1 := fun i => oneSet_binary _
  have mass : ∀ i,(∫ x,s i x ∂μ)=(1:ℝ)/6 := by
    intro i
    simpa [s,oneSet,integral_indicator (hX i).1,measureReal_def] using (hX i).2
  have orth : ∀ i j,i≠j → ∀ x,s i x*s j x=0 := by
    intro i j hij x
    by_cases hi : x∈X i
    · have hj : x∉X j := fun hj => Set.disjoint_left.mp (hdis hij) hi hj
      simp [s,oneSet,hi,hj]
    · simp [s,oneSet,hi]
  have partition : ∀ᵐ x ∂μ,∑ i,s i x=1 := by
    filter_upwards [hG] with x hx
    rw [←hcover] at hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    rw [Finset.sum_eq_single i]
    · simp [s,oneSet,hi]
    · intro j _ hji
      have hj : x∉X j := fun hj => Set.disjoint_left.mp (hdis hji) hj hi
      simp [s,oneSet,hj]
    · simp
  have table : ∀ i j,∀ᵐ p ∂μ.prod μ,s i p.1=1 → s j p.2=1 → H p=TwoPairPrismFaithfulness.value i j :=
    TwoPairPrismFaithfulness.set_blocks_to_indicator_table μ H hH X (fun i => (hX i).1) htable
  have faithful := TwoPairPrismFaithfulness.actual_rows_faithful μ H s bsm (1/6) (by norm_num) mass table
  have confC := TwoPairPrismConfinement.square_support_confinement μ (W 2) (W 3) P L
    (hm 2) (hm 3) hP hL (hb 2) (hb 3) facts.p_cap (hs 2) (hs 3) sP
    (hr 2) (hr 3) (Filter.Eventually.of_forall (fun _ => rfl)) facts.zero_p facts.half
  have confD := TwoPairPrismConfinement.square_support_confinement μ (W 3) (W 2) P L
    (hm 3) (hm 2) hP hL (hb 3) (hb 2) facts.p_cap (hs 3) (hs 2) sP
    (hr 3) (hr 2) (Filter.Eventually.of_forall (fun p => add_comm _ _)) facts.zero_p facts.half
  have square_zero (K : Ω×Ω→ℝ) (hK : Measurable K) (bK : ∀ p,0≤K p)
      (conf : ∀ᵐ p ∂μ.prod μ,0<K p → (fun z => H (p.1,z)) =ᵐ[μ] (fun z => H (p.2,z))) :
      ∀ i j,i≠j → ∀ᵐ p ∂μ.prod μ,s i p.1*K p*s j p.2=0 := by
    intro i j hij
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((((hsm i).comp measurable_fst).mul hK).mul ((hsm j).comp measurable_snd)) measurable_const)).mpr
    filter_upwards [faithful i j,Measure.ae_ae_of_ae_prod conf] with x hx hc
    filter_upwards [hx,hc] with y hy hc
    rcases bsm i x with hi|hi
    · simp [hi]
    rcases bsm j y with hj|hj
    · simp [hj]
    have hk : K (x,y)=0 := by
      by_contra hn
      exact hij ((hy hi hj).1 (hc (lt_of_le_of_ne (bK _) (Ne.symm hn))))
    simp [hk]
  have cc := square_zero (comp μ (W 2) (W 2)) (measurable_comp μ _ _ (hm 2) (hm 2))
    (fun p => (comp_bounds μ _ _ (hm 2) (hm 2) (hb 2) (hb 2) p).1) confC
  have dd := square_zero (comp μ (W 3) (W 3)) (measurable_comp μ _ _ (hm 3) (hm 3))
    (fun p => (comp_bounds μ _ _ (hm 3) (hm 3) (hb 3) (hb 3) p).1) confD
  have lzero : ∀ i j,j≠TwoPairPrismFinite.flip i → ∀ᵐ p ∂μ.prod μ,s i p.1*L p*s j p.2=0 := by
    intro i j hij
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((((hsm i).comp measurable_fst).mul hL).mul ((hsm j).comp measurable_snd)) measurable_const)).mpr
    filter_upwards [faithful i j,facts.complementary] with x hx hc
    filter_upwards [hx,hc] with y hy hc
    rcases bsm i x with hi|hi
    · simp [hi]
    rcases bsm j y with hj|hj
    · simp [hj]
    have hl : L (x,y)=0 := by
      by_contra hn
      exact hij ((hy hi hj).2 (hc (lt_of_le_of_ne (facts.l_cap _).1 (Ne.symm hn))))
    simp [hl]
  have pzero : ∀ i j,¬prism i j → ∀ᵐ p ∂μ.prod μ,s i p.1=1 → s j p.2=1 → P p=0 := by
    intro i j hij
    filter_upwards [table i j] with p hp
    intro hi hj
    have hh := hp hi hj
    have hn : ¬0<P p := by
      intro hpos
      simp [H,supportKernel,hpos,TwoPairPrismFaithfulness.value,hij] at hh
    exact le_antisymm (le_of_not_gt hn) (facts.p_cap p).1
  exact TwoPairPrismAssembly.prism_impossible μ (W 0) (W 1) (W 2) (W 3) P s
    (hm 0) (hm 1) (hm 2) (hm 3) hsm (hb 0) (hb 1) (hb 2) (hb 3)
    (hs 0) (hs 1) (hs 2) (hs 3) bsm orth partition mass (hr 0) (hr 2) (hr 3) cc dd lzero
    (Filter.Eventually.of_forall (fun p => by linarith [hpart p]))
    (Filter.Eventually.of_forall (fun _ => rfl)) pzero facts.four_cycles.2.1
end TwoPairNormalizedPrism
end


-- Local module: E811TwoPairParityComplete
section

open MeasureTheory
open scoped BigOperators

namespace Submissions.E811TwoPairParity.Complete

/-- Two copies each of the first two kernels, then the two singleton kernels. -/
def color : Fin 6 → Fin 4 := ![0, 0, 1, 1, 2, 3]

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (color (σ 0)) (x₀, x₁) * W (color (σ 1)) (x₁, x₂) *
    W (color (σ 2)) (x₂, x₃) * W (color (σ 3)) (x₃, x₄) *
    W (color (σ 4)) (x₄, x₅) * W (color (σ 5)) (x₅, x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

noncomputable def sameSide {Ω : Type*} (S : Set Ω) (p : Ω × Ω) : ℝ := by
  classical
  exact if (p.1 ∈ S ↔ p.2 ∈ S) then 1 else 0

/-- Balanced rainbow-C6-free kernels with two identical pairs admit a 3+3 parity cut. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 4 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂μ.prod μ, 2 * W 0 p + 2 * W 1 p + W 2 p + W 3 p = 1) →
      (∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x, y) ∂μ) = (1 / 6 : ℝ)) →
      (∀ σ : Equiv.Perm (Fin 6), cycleDensity μ W σ = 0) →
      ∃ S : Set Ω, MeasurableSet S ∧ μ.real S = (1 / 2 : ℝ) ∧
        ∃ c : Fin 4, (c = 2 ∨ c = 3) ∧
          ((∀ᵐ p ∂μ.prod μ, 2 * W 0 p + W c p = sameSide S p) ∨
           (∀ᵐ p ∂μ.prod μ, 2 * W 0 p + W c p = 1 - sameSide S p))

theorem target : statement := by
  intro Ω _ μ hμ W hm hb hs hp hr hz
  letI : IsProbabilityMeasure μ := hμ
  have hz' : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (TwoPairWords.color (σ i)))=0 := by
    intro σ
    simpa only [cycleDensity,color,TwoPairWords.color,LowSupportCycle.cycleNested] using hz σ
  obtain ⟨V,hVm,hVb,hVs,hVp,hVe,hVr,hVz,hshape⟩ :=
    TwoPairStructuralReduction.structural_reduction μ W hm hb hs hr hp hz'
  have facts := TwoPairStructuralReduction.normalized_analytic_facts μ V hVm hVb hVs hVr hVp hVz
  have hout : ∃ S : Set Ω, MeasurableSet S ∧ μ.real S=(1:ℝ)/2 ∧ ∃ c : Bool,
      ((∀ᵐ p ∂μ.prod μ, 2*V 0 p+(if c then V 3 p else V 2 p)=sameSide S p) ∨
       (∀ᵐ p ∂μ.prod μ, 2*V 0 p+(if c then V 3 p else V 2 p)=1-sameSide S p)) := by
    rcases hshape with ⟨S,hS,mS,hcut⟩ | ⟨G,hGm,hG,X,hX,hdis,hcover,htable⟩
    · obtain ⟨c,hc⟩ := TwoPairNormalizedCut.normalized_cut_parity μ V hVm hVb hVs hVr hVp
        facts S hS mS hcut
      exact ⟨S,hS,mS,c,by simpa only [sameSide] using hc⟩
    · exact False.elim (TwoPairNormalizedPrism.normalized_prism_impossible μ V hVm hVb hVs hVr hVp
        facts G hG X hX hdis hcover (by
          intro i j
          filter_upwards [htable i j] with p hp
          by_cases hij : TwoPairAntipodal.prism i j
          · simpa only [if_pos hij] using hp
          · simpa only [if_neg hij] using hp))
  obtain ⟨S,hS,mS,c,hc⟩ := hout
  have hec : (fun p => if c then V 3 p else V 2 p) =ᵐ[μ.prod μ]
      (fun p => W (if c then 3 else 2) p) := by
    cases c
    · simpa using hVe 2
    · simpa using hVe 3
  refine ⟨S,hS,mS,(if c then 3 else 2),?_,?_⟩
  · cases c <;> simp
  · rcases hc with hc | hc
    · left
      filter_upwards [hc,hVe 0,hec] with p hp h0 hchoice
      change (if c then V 3 p else V 2 p)=W (if c then 3 else 2) p at hchoice
      rw [h0,hchoice] at hp
      exact hp
    · right
      filter_upwards [hc,hVe 0,hec] with p hp h0 hchoice
      change (if c then V 3 p else V 2 p)=W (if c then 3 else 2) p at hchoice
      rw [h0,hchoice] at hp
      exact hp

end Submissions.E811TwoPairParity.Complete

end
