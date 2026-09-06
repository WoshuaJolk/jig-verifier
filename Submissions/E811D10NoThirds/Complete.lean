import Mathlib
import Mathlib.Probability.ConditionalProbability

/- Inlined module LowSupportAnalysis; original SHA256 2f4cfe2a13bf7780bc3891de0e5112d9ef08abd58162426a3517c6c2a33b3513 -/
section JigBundleModule0
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


end JigBundleModule0

/- Inlined module FourColorKernels; original SHA256 3928c57e248cee0bd5e1a6870e510570baf5fc73eedc73ba4edb92364633e973 -/
section JigBundleModule1
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
end JigBundleModule1

/- Inlined module TwoPairHalfTransport; original SHA256 c8eb33ce5117cdcdcab9bea0534aa14ba82e37654b0d17699be1d1e4ae37c6f9 -/
section JigBundleModule2
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

end JigBundleModule2

/- Inlined module TwoPairHalfSetOperator; original SHA256 7d78c750ed203ddf5f84a28397b1d758c887016c979de4b80d708360adbf9405 -/
section JigBundleModule3
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
end JigBundleModule3

/- Inlined module D10BlockIntegrals; original SHA256 05b2e988cd2111bc2be4823c59fec83136afb69fa9416b768d47609e9e6369ee -/
section JigBundleModule4
open MeasureTheory
namespace D10BlockIntegrals
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
noncomputable def block (W : Fin 6 → Ω×Ω → ℝ) (T : Fin 6 → Set Ω) (d : ℝ) (c i j : Fin 6) : ℝ :=
  (∫ p in (T i ×ˢ T j), W c p ∂μ.prod μ)/(d*d)
lemma integrable (W : Ω×Ω → ℝ) (hW : Measurable W)
    (bW : ∀ᵐ p ∂μ.prod μ, 0≤W p ∧ W p≤1) : Integrable W (μ.prod μ) :=
  LowSupportAnalysis.unit_integrable_ae hW bW
lemma nonneg (W : Fin 6 → Ω×Ω → ℝ)
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (T : Fin 6 → Set Ω) (d : ℝ) (c i j : Fin 6) : 0≤block μ W T d c i j := by
  apply div_nonneg
  · exact integral_nonneg_of_ae ((ae_restrict_of_ae (bW c)).mono (fun _ h => h.1))
  · exact mul_self_nonneg d
lemma part (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (hp : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (T : Fin 6 → Set Ω) (d : ℝ) (hd : d≠0) (mT : ∀ i, μ.real (T i)=d)
    (i j : Fin 6) : ∑ c, block μ W T d c i j=1 := by
  simp only [block,← Finset.sum_div]
  rw [← integral_finset_sum _ (fun c _ => (integrable μ (W c) (hW c) (bW c)).integrableOn)]
  rw [integral_congr_ae (ae_restrict_of_ae hp)]
  have mt (i) : (μ (T i)).toReal=d := mT i
  simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter,smul_eq_mul,mul_one,measureReal_def]
  rw [Measure.prod_prod (μ := μ) (ν := μ) (T i) (T j)]
  simp [ENNReal.toReal_mul,mt,hd]
lemma full (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i)) (d : ℝ)
    (mT : ∀ i, μ.real (T i)=d) (c i j : Fin 6) (hfull : block μ W T d c i j=1) :
    ∀ᵐ p ∂μ.prod μ, p.1∈T i → p.2∈T j → W c p=1 := by
  have hi := (integrable μ (W c) (hW c) (bW c)).integrableOn (s := (T i ×ˢ T j))
  have hd : d*d≠0 := by intro hz; simp [block,hz] at hfull
  have he : (∫ p in (T i ×ˢ T j), W c p ∂μ.prod μ)=d*d := (div_eq_one_iff_eq hd).mp hfull
  have hconst : (∫ _ in (T i ×ˢ T j), (1:ℝ) ∂μ.prod μ)=d*d := by
    have mt (i) : (μ (T i)).toReal=d := mT i
    simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter,smul_eq_mul,mul_one,measureReal_def]
    rw [Measure.prod_prod (μ := μ) (ν := μ) (T i) (T j)]
    simp [ENNReal.toReal_mul,mt]
  have hh := (integral_eq_iff_of_ae_le hi (integrable_const (1:ℝ))
    ((ae_restrict_of_ae (bW c)).mono (fun _ h => h.2))).mp (he.trans hconst.symm)
  have h := (ae_restrict_iff' ((hT i).prod (hT j))).mp hh
  filter_upwards [h] with p hp
  exact fun hi hj => hp ⟨hi,hj⟩
end D10BlockIntegrals
end JigBundleModule4

/- Inlined module D10BlockRows; original SHA256 7c26481c494e658d643c96f811498bed6b24253fb154574f84c287ca03acf87c -/
section JigBundleModule5
open MeasureTheory
namespace D10BlockRows
open D10BlockIntegrals TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma symmetry (W : Fin 6 → Ω×Ω → ℝ)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (T : Fin 6 → Set Ω) (d : ℝ) (c i j : Fin 6) : block μ W T d c i j=block μ W T d c j i := by
  unfold block
  congr 1
  calc
    _ = ∫ p in (T i) ×ˢ (T j), W c p.swap ∂μ.prod μ := integral_congr_ae (ae_restrict_of_ae (sW c))
    _ = _ := setIntegral_prod_swap (T j) (T i) (W c)
lemma partition_integral (F : Ω×Ω → ℝ) (hF : Integrable F (μ.prod μ))
    (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hp : ∀ᵐ y ∂μ, ∑ j, oneSet (T j) y=1) (i : Fin 6) :
    (∑ j, ∫ p in (T i) ×ˢ (T j), F p ∂μ.prod μ)=∫ p in (T i) ×ˢ Set.univ, F p ∂μ.prod μ := by
  have hi (j : Fin 6) := hF.indicator ((hT i).prod (hT j))
  simp_rw [← integral_indicator ((hT i).prod (hT _))]
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  rw [← integral_indicator ((hT i).prod MeasurableSet.univ)]
  apply integral_congr_ae
  have hp' := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hp
  filter_upwards [hp'] with p hp
  by_cases hx : p.1∈T i
  · have eq (j : Fin 6) : ((T i) ×ˢ (T j)).indicator F p=oneSet (T j) p.2 * F p := by
      by_cases hy : p.2∈T j <;> simp [Set.indicator,Set.mem_prod,hx,hy,oneSet]
    simp only [eq,← Finset.sum_mul,hp,one_mul]
    simp [Set.indicator,Set.mem_prod,hx]
  · have eq (j : Fin 6) : ((T i) ×ˢ (T j)).indicator F p=0 := by simp [Set.indicator,Set.mem_prod,hx]
    simp [eq,Set.indicator,Set.mem_prod,hx]
lemma rows (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (degree : ∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x,y) ∂μ)= (1:ℝ)/6)
    (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (mT : ∀ i, μ.real (T i)=(1:ℝ)/6)
    (hp : ∀ᵐ y ∂μ, ∑ j, oneSet (T j) y=1) (c i : Fin 6) :
    ∑ j, block μ W T ((1:ℝ)/6) c i j=1 := by
  simp only [block,← Finset.sum_div]
  rw [partition_integral μ (W c) (integrable μ (W c) (hW c) (bW c)) T hT hp i]
  rw [setIntegral_prod _ (integrable μ (W c) (hW c) (bW c)).integrableOn]
  simp only [Measure.restrict_univ]
  rw [integral_congr_ae (ae_restrict_of_ae (degree c))]
  simp [mT]
end D10BlockRows
end JigBundleModule5

/- Inlined module D10TargetDisjoint; original SHA256 be36bfdfc5c5eb18523d1c0c5946e092ba9bf15d31d41ac009f9517fb770eb1c -/
section JigBundleModule6
open MeasureTheory
namespace D10TargetDisjoint
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω]
lemma indicator (T : Fin 6 → Set Ω) (y : Ω) (hp : ∑ c, oneSet (T c) y=1)
    (j : Fin 6) (hy : y∈T j) (c : Fin 6) : oneSet (T c) y=if c=j then 1 else 0 := by
  by_cases hc : c=j
  · subst c; simp [oneSet,hy]
  rw [if_neg hc]
  have full : oneSet (T j) y=1 := by simp [oneSet,hy]
  have eq := Finset.sum_erase_add Finset.univ (fun k => oneSet (T k) y) (Finset.mem_univ j)
  rw [hp,full] at eq
  have hz : ∑ k ∈ Finset.univ.erase j, oneSet (T k) y=0 := by linarith
  have hmem : c∈Finset.univ.erase j := by simp [hc]
  have hle := Finset.single_le_sum (s := Finset.univ.erase j) (f := fun k => oneSet (T k) y)
    (fun k _ => (oneSet_bounds (T k) y).1) hmem
  rw [hz] at hle
  exact le_antisymm hle (oneSet_bounds (T c) y).1
end D10TargetDisjoint
end JigBundleModule6

/- Inlined module D10BlockRoot; original SHA256 5c7fa404ca6823bbd78c2e5d8e0e954a381b8ee861c6635e78395256ebb20c22 -/
section JigBundleModule7
open MeasureTheory
namespace D10BlockRoot
open D10BlockIntegrals TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma constant (W : Fin 6 → Ω×Ω → ℝ) (T : Fin 6 → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (mT : ∀ i, μ.real (T i)=(1:ℝ)/6)
    (c i j : Fin 6) (v : ℝ)
    (he : ∀ᵐ p ∂μ.prod μ, p.1∈T i → p.2∈T j → W c p=v) :
    block μ W T ((1:ℝ)/6) c i j=v := by
  have hh : W c =ᵐ[(μ.prod μ).restrict (T i ×ˢ T j)] (fun _ => v) := by
    apply (ae_restrict_iff' ((hT i).prod (hT j))).mpr
    filter_upwards [he] with p hp
    exact fun h => hp h.1 h.2
  unfold block
  rw [integral_congr_ae hh]
  have mt (i) : (μ (T i)).toReal=(1:ℝ)/6 := mT i
  simp [measureReal_def,ENNReal.toReal_mul,mt]
lemma root (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (S : Set Ω) (hS : MeasurableSet S) (T : Fin 6 → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (mT : ∀ i, μ.real (T i)=(1:ℝ)/6)
    (part : ∀ᵐ y ∂μ, ∑ j, oneSet (T j) y=1)
    (twins : ∀ c, ∀ᵐ x ∂μ.restrict S, (fun y => W c (x,y)) =ᵐ[μ] oneSet (T c))
    (r : Fin 6) (hroot : S =ᵐ[μ] T r) (c j : Fin 6) :
    block μ W T ((1:ℝ)/6) c r j=if c=j then 1 else 0 := by
  apply constant μ W T hT mT
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  have ht := (ae_restrict_iff' hS).mp (twins c)
  filter_upwards [ht,hroot] with x hx hs
  by_cases hi : x∈T r
  · have hxS : x∈S := hs.mpr hi
    filter_upwards [hx hxS,part] with y hy hp
    exact fun _ hj => hy.trans (D10TargetDisjoint.indicator T y hp j hj c)
  · exact Filter.Eventually.of_forall (fun y h => (hi h).elim)
end D10BlockRoot
end JigBundleModule7

/- Inlined module D10TwinTargets; original SHA256 095bac1845f7efc2a3065b1a08c841a218a58c716bb3f54dcca404578877126a -/
section JigBundleModule8
open MeasureTheory
namespace D10TwinTargets
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma targets (W : Fin 6 → Ω×Ω → ℝ) (d : ℝ)
    (degree : ∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x,y) ∂μ)=d)
    (part : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S : Set Ω) (pS : μ S ≠ 0)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (twins : ∀ c, ∀ᵐ x ∂μ.restrict S, (fun y => W c (x,y)) =ᵐ[μ] oneSet (T c)) :
    (∀ c, μ.real (T c)=d) ∧ (∀ᵐ y ∂μ, ∑ c, oneSet (T c) y=1) := by
  have hn : μ.restrict S ≠ 0 := by
    intro hz
    apply pS
    simpa using congrArg (fun m : Measure Ω => m Set.univ) hz
  letI : NeZero (μ.restrict S) := ⟨hn⟩
  constructor
  · intro c
    obtain ⟨x,hx,hdeg⟩ := ((twins c).and (ae_restrict_of_ae (degree c))).exists
    rw [integral_congr_ae hx] at hdeg
    simpa [oneSet,integral_indicator (hT c)] using hdeg
  · have hall := ae_all_iff.mpr twins
    have hp := Measure.ae_ae_of_ae_prod part
    obtain ⟨x,hx,hpart⟩ := (hall.and (ae_restrict_of_ae hp)).exists
    have hh := ae_all_iff.mpr hx
    filter_upwards [hh,hpart] with y hy hpy
    simpa only [hy] using hpy
end D10TwinTargets
end JigBundleModule8

/- Inlined module TwoPairTwinRectangles; original SHA256 b3304c5323e16856c433ec77539954869f7222e6009f7c808eae12e7afc7f95f -/
section JigBundleModule9
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
end JigBundleModule9

/- Inlined module D10TwinRectangle; original SHA256 c8a8486a83fc1c56f6dc51c00cf099fa57dbda42b8a87cfb10e5fe1decacc95c -/
section JigBundleModule10
open MeasureTheory TwoPairTwinRectangles
namespace D10TwinRectangle
variable {Ω : Type*} [MeasurableSpace Ω]
theorem twin_rectangle_constant (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω × Ω → ℝ) (hH : Measurable H)
    (sH : ∀ᵐ p ∂μ.prod μ, H p=H (p.2,p.1))
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
    · have hsym := Measure.ae_ae_of_ae_prod sH
      filter_upwards [rY, ae_restrict_of_ae hsym] with y hy sy
      filter_upwards [ae_restrict_of_ae hy, ae_restrict_of_ae sy] with x hx hs
      exact hs.symm.trans hx
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

end D10TwinRectangle
end JigBundleModule10

/- Inlined module D10TwinInternal; original SHA256 aa9d64baeb135ce7e48a2448ae3d344dcbcd93d7fb6ae12a97beb71653a3b354 -/
section JigBundleModule11
open MeasureTheory
namespace D10TwinInternal
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma internal (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (S : Set Ω) (hS : MeasurableSet S) (pS : 0 < μ S)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (mT : ∀ c, μ (T c)=μ S)
    (part : ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=1)
    (twins : ∀ c, ∀ᵐ x ∂μ.restrict S, (fun y => W c (x,y)) =ᵐ[μ] oneSet (T c)) :
    ∃ r : Fin 6, S =ᵐ[μ] T r := by
  have hc (c : Fin 6) : ∃ b : ℝ, (b=0 ∨ b=1) ∧ oneSet (T c) =ᵐ[μ.restrict S] (fun _ => b) := by
    obtain ⟨b,hb,_,hf,_⟩ := D10TwinRectangle.twin_rectangle_constant μ (W c) (hW c) (sW c)
      S S pS pS (oneSet (T c)) (oneSet (T c)) (oneSet_measurable _ (hT c))
      (oneSet_measurable _ (hT c)) (Filter.Eventually.of_forall (fun x => by
        by_cases hx : x∈T c <;> simp [oneSet,hx])) (twins c) (twins c)
    exact ⟨b,hb,hf⟩
  choose b hb he using hc
  have hn : μ.restrict S ≠ 0 := by
    intro hz
    have hm : μ S=0 := by simpa using congrArg (fun m : Measure Ω => m Set.univ) hz
    exact (ne_of_gt pS) hm
  letI : NeZero (μ.restrict S) := ⟨hn⟩
  have hall : ∀ᵐ x ∂μ.restrict S, ∀ c, oneSet (T c) x=b c := ae_all_iff.mpr he
  obtain ⟨x,hx,hp⟩ := (hall.and (ae_restrict_of_ae part)).exists
  have sum : ∑ c, b c=1 := by simpa only [hx] using hp
  have ex : ∃ c, b c=1 := by
    by_contra! h
    have zz : ∀ c, b c=0 := fun c => (hb c).resolve_right (h c)
    simp only [zz,Finset.sum_const_zero] at sum
    norm_num at sum
  obtain ⟨r,hr⟩ := ex
  refine ⟨r,?_⟩
  have sub : S ≤ᵐ[μ] T r := by
    have ht : ∀ᵐ x ∂μ.restrict S, x∈T r := by
      filter_upwards [he r] with x hx
      rw [hr] at hx
      by_contra hn
      simp [oneSet,hn] at hx
    exact (ae_restrict_iff' hS).mp ht
  exact ae_eq_of_ae_subset_of_measure_ge sub (mT r).le hS.nullMeasurableSet (measure_ne_top μ _)
end D10TwinInternal
end JigBundleModule11

/- Inlined module TwoPairHalfSupport; original SHA256 cff73d4d5e87cde231251d740b9bf57f254083cdfe8633e5f18be23e250be3df -/
section JigBundleModule12
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
end JigBundleModule12

/- Inlined module TwoPairCompositionAlgebra; original SHA256 abdbc52a07f89b982f919fa58e6ee9ff7d7c29a4240b1a63f582a584d570c8a1 -/
section JigBundleModule13
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
end JigBundleModule13

/- Inlined module TwoPairSandwich; original SHA256 d7359af606fdce0e0e3944b3e6c2834043c5bdd53a5b84c620886fffc98bdc02 -/
section JigBundleModule14
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
end JigBundleModule14

/- Inlined module TwoPairTraceAlgebra; original SHA256 4d5d2ca39b6f89fa9d0b963fd5be584f2ea80bfca58b4d0e2215aedccd765d52 -/
section JigBundleModule15
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
end JigBundleModule15

/- Inlined module LowSupportCycle; original SHA256 4f42d9037372079626bfce46da9249fc8990a31e98fbe750afe01335ada6abe6 -/
section JigBundleModule16
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
end JigBundleModule16

/- Inlined module LowSupportPaths; original SHA256 7482f1853cbeb93fc44e4e0304d6c1419bc0caaf2449af77dc962200edf9798e -/
section JigBundleModule17

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


end JigBundleModule17

/- Inlined module LowSupportRepresentatives; original SHA256 e7719b5204901928342aed1cbd5eb7c89afb831a08bd7c84eec274b1e4b553e8 -/
section JigBundleModule18

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

end JigBundleModule18

/- Inlined module LowSupportCyclePath; original SHA256 3c07412e1edffd0c55f4e50afff4ad29db10b2ad8a1cc3b84a1aa300653cdeb5 -/
section JigBundleModule19
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
end JigBundleModule19

/- Inlined module FourColorBlock; original SHA256 9d3eeaddc59fe015db555a1c87531dcd3295434e15de0803bdfc819b87c9399a -/
section JigBundleModule20

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
end JigBundleModule20

/- Inlined module FourColorTwinBlock; original SHA256 3eb7a0ca7cc5a881aef7ef80071bfb22ed55a2b9930f6b2a934b2867564a2d0a -/
section JigBundleModule21
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
end JigBundleModule21

/- Inlined module TwoPairDoubledDisjoint; original SHA256 26910e587902533555334aac97ffe5276e6b5392fedae8bb96c9be2617f0022d -/
section JigBundleModule22
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
end TwoPairDoubledDisjoint
end JigBundleModule22

/- Inlined module FourColorKernelMatrix; original SHA256 e871c79f4ad3d151b84f753546dabca7c09ba6a4221883c19f5bbb7c093e072f -/
section JigBundleModule23
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
end JigBundleModule23

/- Inlined module FourColorRepresentatives; original SHA256 1ae0253dabd2693a2b0a3f03b7f6ca26e8372c9a0faf5a28575de1155853fe11 -/
section JigBundleModule24
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
end JigBundleModule24

/- Inlined module FourColorCycleMatrix; original SHA256 b03ed3d16464a4f747ea5c04694e227bcb8ff0321f4028d6bf2572b8a566923e -/
section JigBundleModule25
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
end JigBundleModule25

/- Inlined module ThirdsAnchoredCycle; original SHA256 9a416e31653ba9e33dc7c2cafd548b22425474c4c378fe40e41de7c1801f3842 -/
section JigBundleModule26
open MeasureTheory
namespace ThirdsAnchoredCycle
open FourColorKernels LowSupportCycle
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma adjacent_reorder (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    LowSupportCycle.cycleNested (μ := μ) W = ∫ u, ∫ v, cycle4 μ (W 0) (W 1) (fun p => W 2 (p.1,v)*W 3 (v,p.2)) (fun p => W 4 (p.1,u)*W 5 (u,p.2)) ∂μ ∂μ := by
  unfold LowSupportCycle.cycleNested cycle4
  calc
    _ = ∫ x, ∫ y, ∫ z, ∫ v, ∫ u, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
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
      intro v
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,p.1)*W 4 (p.1,p.2)*W 5 (p.2,x) ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ x, ∫ y, ∫ z, ∫ u, ∫ v, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,p.1)*W 3 (p.1,t)*W 4 (t,p.2)*W 5 (p.2,x) ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ x, ∫ y, ∫ u, ∫ z, ∫ v, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ v, ∫ t, W 0 (x,y)*W 1 (y,p.1)*W 2 (p.1,v)*W 3 (v,t)*W 4 (t,p.2)*W 5 (p.2,x) ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ x, ∫ u, ∫ y, ∫ z, ∫ v, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ z, ∫ v, ∫ t, W 0 (x,p.1)*W 1 (p.1,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,p.2)*W 5 (p.2,x) ∂μ ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ x, ∫ y, ∫ z, ∫ v, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ y, ∫ z, ∫ v, ∫ t, W 0 (p.1,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,p.2)*W 5 (p.2,p.1) ∂μ ∂μ ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ x, ∫ y, ∫ v, ∫ z, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ t, W 0 (x,y)*W 1 (y,p.1)*W 2 (p.1,p.2)*W 3 (p.2,t)*W 4 (t,u)*W 5 (u,x) ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ x, ∫ v, ∫ y, ∫ z, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ z, ∫ t, W 0 (x,p.1)*W 1 (p.1,z)*W 2 (z,p.2)*W 3 (p.2,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ v, ∫ x, ∫ y, ∫ z, ∫ t, W 0 (x,y)*W 1 (y,z)*W 2 (z,v)*W 3 (v,t)*W 4 (t,u)*W 5 (u,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ y, ∫ z, ∫ t, W 0 (p.1,y)*W 1 (y,z)*W 2 (z,p.2)*W 3 (p.2,t)*W 4 (t,u)*W 5 (u,p.1) ∂μ ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v
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
      intro t
      dsimp only
      ring

lemma adjacent_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, cycle4 μ (W 0) (W 1) (fun p => W 2 (p.1,v)*W 3 (v,p.2)) (fun p => W 4 (p.1,u)*W 5 (u,p.2))=0 := by
  rw [adjacent_reorder μ W hm hb] at hz
  have hu := (TwoPairDoubledDisjoint.unit_zero_iff μ (fun u => ∫ v, cycle4 μ (W 0) (W 1) (fun p => W 2 (p.1,v)*W 3 (v,p.2)) (fun p => W 4 (p.1,u)*W 5 (u,p.2)) ∂μ)
    (by unfold cycle4; fun_prop) (by
      intro u
      unfold cycle4
      repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
        apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)).mp hz
  filter_upwards [hu] with u hu
  exact (TwoPairDoubledDisjoint.unit_zero_iff μ (fun v => cycle4 μ (W 0) (W 1) (fun p => W 2 (p.1,v)*W 3 (v,p.2)) (fun p => W 4 (p.1,u)*W 5 (u,p.2)))
    (by unfold cycle4; fun_prop) (by
      intro v
      unfold cycle4
      repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
        apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)).mp hu

lemma alternating_reorder (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    LowSupportCycle.cycleNested (μ := μ) W = ∫ u, ∫ v, cycle4 μ (W 0) (fun p => W 1 (p.1,u)*W 2 (u,p.2)) (W 3) (fun p => W 4 (p.1,v)*W 5 (v,p.2)) ∂μ ∂μ := by
  unfold LowSupportCycle.cycleNested cycle4
  calc
    _ = ∫ x, ∫ u, ∫ y, ∫ z, ∫ t, ∫ v, W 0 (x,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ z, ∫ t, ∫ v, W 0 (x,p.1)*W 1 (p.1,p.2)*W 2 (p.2,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,x) ∂μ ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ x, ∫ y, ∫ z, ∫ t, ∫ v, W 0 (x,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ y, ∫ z, ∫ t, ∫ v, W 0 (p.1,y)*W 1 (y,p.2)*W 2 (p.2,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,p.1) ∂μ ∂μ ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ x, ∫ y, ∫ z, ∫ v, ∫ t, W 0 (x,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => W 0 (x,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,p.1)*W 4 (p.1,p.2)*W 5 (p.2,x) ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ x, ∫ y, ∫ v, ∫ z, ∫ t, W 0 (x,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ t, W 0 (x,y)*W 1 (y,u)*W 2 (u,p.1)*W 3 (p.1,t)*W 4 (t,p.2)*W 5 (p.2,x) ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ x, ∫ v, ∫ y, ∫ z, ∫ t, W 0 (x,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ z, ∫ t, W 0 (x,p.1)*W 1 (p.1,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,p.2)*W 5 (p.2,x) ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = ∫ u, ∫ v, ∫ x, ∫ y, ∫ z, ∫ t, W 0 (x,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,v)*W 5 (v,x) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      exact integral_integral_swap (unit_integrable (μ.prod μ)
        (fun p : Ω × Ω => ∫ y, ∫ z, ∫ t, W 0 (p.1,y)*W 1 (y,u)*W 2 (u,z)*W 3 (z,t)*W 4 (t,p.2)*W 5 (p.2,p.1) ∂μ ∂μ ∂μ) (by fun_prop) (by
          intro p
          repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
            apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q))
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v
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
      intro t
      dsimp only
      ring

lemma alternating_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, cycle4 μ (W 0) (fun p => W 1 (p.1,u)*W 2 (u,p.2)) (W 3) (fun p => W 4 (p.1,v)*W 5 (v,p.2))=0 := by
  rw [alternating_reorder μ W hm hb] at hz
  have hu := (TwoPairDoubledDisjoint.unit_zero_iff μ (fun u => ∫ v, cycle4 μ (W 0) (fun p => W 1 (p.1,u)*W 2 (u,p.2)) (W 3) (fun p => W 4 (p.1,v)*W 5 (v,p.2)) ∂μ)
    (by unfold cycle4; fun_prop) (by
      intro u
      unfold cycle4
      repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
        apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)).mp hz
  filter_upwards [hu] with u hu
  exact (TwoPairDoubledDisjoint.unit_zero_iff μ (fun v => cycle4 μ (W 0) (fun p => W 1 (p.1,u)*W 2 (u,p.2)) (W 3) (fun p => W 4 (p.1,v)*W 5 (v,p.2)))
    (by unfold cycle4; fun_prop) (by
      intro v
      unfold cycle4
      repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit |
        apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)).mp hu
end ThirdsAnchoredCycle
end JigBundleModule26

/- Inlined module ThirdsFourCycleZero; original SHA256 1e9649e1c400c809926a13e628df08d47aff47559b6523bd0d03f3e7bc81de09 -/
section JigBundleModule27
open MeasureTheory
namespace ThirdsFourCycleZero
open FourColorKernels
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma zero_iff (f g h k : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (bf : ∀ p, 0≤f p ∧ f p≤1) (bg : ∀ p, 0≤g p ∧ g p≤1)
    (bh : ∀ p, 0≤h p ∧ h p≤1) (bk : ∀ p, 0≤k p ∧ k p≤1) :
    cycle4 μ f g h k=0 ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ᵐ t ∂μ,
      f (x,y)*g (y,z)*h (z,t)*k (t,x)=0 := by
  unfold cycle4
  rw [TwoPairDoubledDisjoint.unit_zero_iff μ _ (by fun_prop) (by
    intro x
    repeat' first | exact bf _ | exact bg _ | exact bh _ | exact bk _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with x
  rw [TwoPairDoubledDisjoint.unit_zero_iff μ _ (by fun_prop) (by
    intro y
    repeat' first | exact bf _ | exact bg _ | exact bh _ | exact bk _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with y
  rw [TwoPairDoubledDisjoint.unit_zero_iff μ _ (by fun_prop) (by
    intro z
    repeat' first | exact bf _ | exact bg _ | exact bh _ | exact bk _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with z
  rw [TwoPairDoubledDisjoint.unit_zero_iff μ _ (by fun_prop) (by
    intro t
    repeat' first | exact bf _ | exact bg _ | exact bh _ | exact bk _ | apply LowSupportAnalysis.mul_unit)]

lemma adjacent_sum_zero (f g : Ω × Ω → ℝ) (h k : Bool → Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : ∀ b, Measurable (h b)) (hk : ∀ b, Measurable (k b))
    (bf : ∀ p, 0≤f p ∧ f p≤1) (bg : ∀ p, 0≤g p ∧ g p≤1)
    (bh : ∀ b p, 0≤h b p ∧ h b p≤1) (bk : ∀ b p, 0≤k b p ∧ k b p≤1)
    (hz : ∀ a b, cycle4 μ f g (h a) (k b)=0) :
    cycle4 μ f g (fun p => h false p+h true p) (fun p => k false p+k true p)=0 := by
  have h0 := fun a b => (zero_iff μ f g (h a) (k b) hf hg (hh a) (hk b) bf bg (bh a) (bk b)).mp (hz a b)
  unfold cycle4
  have hp : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ᵐ t ∂μ,
      f (x,y)*g (y,z)*(h false (z,t)+h true (z,t))*(k false (t,x)+k true (t,x))=0 := by
    filter_upwards [h0 false false,h0 false true,h0 true false,h0 true true] with x h00 h01 h10 h11
    filter_upwards [h00,h01,h10,h11] with y h00 h01 h10 h11
    filter_upwards [h00,h01,h10,h11] with z h00 h01 h10 h11
    filter_upwards [h00,h01,h10,h11] with t h00 h01 h10 h11
    nlinarith
  calc
    _ = ∫ x, ∫ y, ∫ z, ∫ t : Ω, (0:ℝ) ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      apply integral_congr_ae
      filter_upwards [hy] with z hz
      exact integral_congr_ae hz
    _ = _ := by simp
lemma alternating_sum_zero (f h : Ω × Ω → ℝ) (g k : Bool → Ω × Ω → ℝ)
    (hf : Measurable f) (hh : Measurable h) (hg : ∀ b, Measurable (g b)) (hk : ∀ b, Measurable (k b))
    (bf : ∀ p, 0≤f p ∧ f p≤1) (bh : ∀ p, 0≤h p ∧ h p≤1)
    (bg : ∀ b p, 0≤g b p ∧ g b p≤1) (bk : ∀ b p, 0≤k b p ∧ k b p≤1)
    (hz : ∀ a b, cycle4 μ f (g a) h (k b)=0) :
    cycle4 μ f (fun p => g false p+g true p) h (fun p => k false p+k true p)=0 := by
  have h0 := fun a b => (zero_iff μ f (g a) h (k b) hf (hg a) hh (hk b) bf (bg a) bh (bk b)).mp (hz a b)
  unfold cycle4
  have hp : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ᵐ t ∂μ,
      f (x,y)*(g false (y,z)+g true (y,z))*h (z,t)*(k false (t,x)+k true (t,x))=0 := by
    filter_upwards [h0 false false,h0 false true,h0 true false,h0 true true] with x h00 h01 h10 h11
    filter_upwards [h00,h01,h10,h11] with y h00 h01 h10 h11
    filter_upwards [h00,h01,h10,h11] with z h00 h01 h10 h11
    filter_upwards [h00,h01,h10,h11] with t h00 h01 h10 h11
    nlinarith
  calc
    _ = ∫ x, ∫ y, ∫ z, ∫ t : Ω, (0:ℝ) ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      apply integral_congr_ae
      filter_upwards [hy] with z hz
      exact integral_congr_ae hz
    _ = _ := by simp
end ThirdsFourCycleZero
end JigBundleModule27

/- Inlined module D10TriangleZero; original SHA256 7e9d4f6208e93d066e17d8c390f3a46a035b0dfab30e8275d8406364f1c27493 -/
section JigBundleModule28
open MeasureTheory
namespace D10TriangleZero
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma zero_iff (f g h : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (bf : ∀ p, 0≤f p ∧ f p≤1) (bg : ∀ p, 0≤g p ∧ g p≤1)
    (bh : ∀ p, 0≤h p ∧ h p≤1) :
    (∫ x, ∫ y, ∫ z, f (x,y)*g (y,z)*h (z,x) ∂μ ∂μ ∂μ)=0 ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      f (x,y)*g (y,z)*h (z,x)=0 := by
  rw [TwoPairDoubledDisjoint.unit_zero_iff μ _ (by fun_prop) (by
    intro x
    repeat' first | exact bf _ | exact bg _ | exact bh _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with x
  rw [TwoPairDoubledDisjoint.unit_zero_iff μ _ (by fun_prop) (by
    intro y
    repeat' first | exact bf _ | exact bg _ | exact bh _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
  apply Filter.eventually_congr
  filter_upwards [] with y
  rw [TwoPairDoubledDisjoint.unit_zero_iff μ _ (by fun_prop) (by
    intro z
    repeat' first | exact bf _ | exact bg _ | exact bh _ | apply LowSupportAnalysis.mul_unit |
      apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)]
end D10TriangleZero
end JigBundleModule28

/- Inlined module ThirdsCanonicalAnchors; original SHA256 3d477e435af553976d3b0b059d95571a76fd96383d987695f0ca21350238677e -/
section JigBundleModule29
open MeasureTheory
namespace ThirdsCanonicalAnchors
open FourColorKernels
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
noncomputable def path (W : Fin 6 → Ω × Ω → ℝ) (i j : Fin 6) (b : Bool) (u : Ω) (p : Ω × Ω) : ℝ :=
  if b then W j (p.1,u)*W i (u,p.2) else W i (p.1,u)*W j (u,p.2)
noncomputable def bridge (W : Fin 6 → Ω × Ω → ℝ) (i j : Fin 6) (u : Ω) (p : Ω × Ω) : ℝ :=
  path W i j false u p+path W i j true u p
lemma path_measurable (W : Fin 6 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (i j : Fin 6) (b : Bool) (u : Ω) : Measurable (path W i j b u) := by
  cases b
  · change Measurable (fun p : Ω × Ω => W i (p.1,u)*W j (u,p.2))
    fun_prop
  · change Measurable (fun p : Ω × Ω => W j (p.1,u)*W i (u,p.2))
    fun_prop
lemma path_bounds (W : Fin 6 → Ω × Ω → ℝ) (hb : ∀ i p, 0≤W i p ∧ W i p≤1)
    (i j : Fin 6) (b : Bool) (u : Ω) (p : Ω × Ω) : 0≤path W i j b u p ∧ path W i j b u p≤1 := by
  cases b <;> exact mul_unit (hb _ _) (hb _ _)
lemma adjacent_word (W : Fin 6 → Ω × Ω → ℝ)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (a b : Bool) : LowSupportCycle.cycleNested (μ := μ)
      ![W 0,W 1,if a then W 5 else W 4,if a then W 4 else W 5,
        if b then W 3 else W 2,if b then W 2 else W 3]=0 := by
  let f : Fin 6 → Fin 6 := ![0,1,if a then 5 else 4,if a then 4 else 5,
    if b then 3 else 2,if b then 2 else 3]
  have hf : Function.Bijective f := by cases a <;> cases b <;> decide
  have h := hz (Equiv.ofBijective f hf)
  have he : (fun i => W ((Equiv.ofBijective f hf) i))=
      ![W 0,W 1,if a then W 5 else W 4,if a then W 4 else W 5,
        if b then W 3 else W 2,if b then W 2 else W 3] := by
    funext i; cases a <;> cases b <;> fin_cases i <;> rfl
  rwa [he] at h
lemma adjacent_anchor_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0≤W i p ∧ W i p≤1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0) :
    ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, cycle4 μ (W 0) (W 1) (bridge W 4 5 v) (bridge W 2 3 u)=0 := by
  have hw (a b : Bool) : ∀ᵐ u ∂μ, ∀ᵐ v ∂μ,
      cycle4 μ (W 0) (W 1) (path W 4 5 a v) (path W 2 3 b u)=0 := by
    let V : Fin 6 → Ω × Ω → ℝ := ![W 0,W 1,if a then W 5 else W 4,if a then W 4 else W 5,
      if b then W 3 else W 2,if b then W 2 else W 3]
    have hV : ∀ i, Measurable (V i) := by
      intro i; cases a <;> cases b <;> fin_cases i <;>
        first | exact hm 0 | exact hm 1 | exact hm 2 | exact hm 3 | exact hm 4 | exact hm 5
    have bV : ∀ i p, 0≤V i p ∧ V i p≤1 := by
      intro i p; cases a <;> cases b <;> fin_cases i <;>
        first | exact hb 0 p | exact hb 1 p | exact hb 2 p | exact hb 3 p | exact hb 4 p | exact hb 5 p
    have h := ThirdsAnchoredCycle.adjacent_zero μ V hV bV (adjacent_word μ W hz a b)
    cases a <;> cases b <;> exact h
  filter_upwards [hw false false,hw false true,hw true false,hw true true] with u h00 h01 h10 h11
  filter_upwards [h00,h01,h10,h11] with v h00 h01 h10 h11
  apply ThirdsFourCycleZero.adjacent_sum_zero μ (W 0) (W 1)
    (fun a => path W 4 5 a v) (fun b => path W 2 3 b u) (hm 0) (hm 1)
    (fun a => path_measurable W hm 4 5 a v) (fun b => path_measurable W hm 2 3 b u)
    (hb 0) (hb 1) (fun a => path_bounds W hb 4 5 a v) (fun b => path_bounds W hb 2 3 b u)
  intro a b
  cases a <;> cases b <;> assumption
lemma alternating_word (W : Fin 6 → Ω × Ω → ℝ)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (a b : Bool) : LowSupportCycle.cycleNested (μ := μ)
      ![W 0,if a then W 3 else W 2,if a then W 2 else W 3,W 1,
        if b then W 5 else W 4,if b then W 4 else W 5]=0 := by
  let f : Fin 6 → Fin 6 := ![0,if a then 3 else 2,if a then 2 else 3,1,
    if b then 5 else 4,if b then 4 else 5]
  have hf : Function.Bijective f := by cases a <;> cases b <;> decide
  have h := hz (Equiv.ofBijective f hf)
  have he : (fun i => W ((Equiv.ofBijective f hf) i))=
      ![W 0,if a then W 3 else W 2,if a then W 2 else W 3,W 1,
        if b then W 5 else W 4,if b then W 4 else W 5] := by
    funext i; cases a <;> cases b <;> fin_cases i <;> rfl
  rwa [he] at h
lemma alternating_anchor_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i)) (hb : ∀ i p, 0≤W i p ∧ W i p≤1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0) :
    ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, cycle4 μ (W 0) (bridge W 2 3 u) (W 1) (bridge W 4 5 v)=0 := by
  have hw (a b : Bool) : ∀ᵐ u ∂μ, ∀ᵐ v ∂μ,
      cycle4 μ (W 0) (path W 2 3 a u) (W 1) (path W 4 5 b v)=0 := by
    let V : Fin 6 → Ω × Ω → ℝ := ![W 0,if a then W 3 else W 2,if a then W 2 else W 3,W 1,
      if b then W 5 else W 4,if b then W 4 else W 5]
    have hV : ∀ i, Measurable (V i) := by
      intro i; cases a <;> cases b <;> fin_cases i <;>
        first | exact hm 0 | exact hm 1 | exact hm 2 | exact hm 3 | exact hm 4 | exact hm 5
    have bV : ∀ i p, 0≤V i p ∧ V i p≤1 := by
      intro i p; cases a <;> cases b <;> fin_cases i <;>
        first | exact hb 0 p | exact hb 1 p | exact hb 2 p | exact hb 3 p | exact hb 4 p | exact hb 5 p
    have h := ThirdsAnchoredCycle.alternating_zero μ V hV bV (alternating_word μ W hz a b)
    cases a <;> cases b <;> exact h
  filter_upwards [hw false false,hw false true,hw true false,hw true true] with u h00 h01 h10 h11
  filter_upwards [h00,h01,h10,h11] with v h00 h01 h10 h11
  apply ThirdsFourCycleZero.alternating_sum_zero μ (W 0) (W 1)
    (fun a => path W 2 3 a u) (fun b => path W 4 5 b v) (hm 0) (hm 1)
    (fun a => path_measurable W hm 2 3 a u) (fun b => path_measurable W hm 4 5 b v)
    (hb 0) (hb 1) (fun a => path_bounds W hb 2 3 a u) (fun b => path_bounds W hb 4 5 b v)
  intro a b
  cases a <;> cases b <;> assumption
end ThirdsCanonicalAnchors
end JigBundleModule29

/- Inlined module TwoPairDenseInvariant; original SHA256 601a7806b46365c31c900252480805466e778b0d3e304dcdf07de9d1b715e58d -/
section JigBundleModule30
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
end JigBundleModule30

/- Inlined module TwoPairBipartiteOrientation; original SHA256 70f3ad2707a5b438eb39ab6e86b8fb220491f4193c2d9de9f417abb637a9cc83 -/
section JigBundleModule31
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


end JigBundleModule31

/- Inlined module ThirdsDeterministicTransport; original SHA256 2b97d18c6071861c02b03ca60a1d3f3c4a37c36bd47c09c5affe4db164250d74 -/
section JigBundleModule32
open MeasureTheory
namespace ThirdsDeterministicTransport
open TwoPairHalfSetOperator
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma act_congr_ae (C D : Ω × Ω → ℝ) (f : Ω → ℝ)
    (he : C =ᵐ[μ.prod μ] D) : act μ C f =ᵐ[μ] act μ D f := by
  filter_upwards [Measure.ae_ae_of_ae_prod he] with x hx
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  simp only [hy]

lemma endpoint_set (f : Ω → ℝ) (hf : Measurable f) (d : ℝ) (hd : d ≠ 0)
    (he : ∀ᵐ x ∂μ, f x = 0 ∨ f x = d) (v : ℝ)
    (hi : (∫ x, f x ∂μ) = d*v) :
    ∃ T : Set Ω, MeasurableSet T ∧ μ.real T = v ∧
      f =ᵐ[μ] (fun x => d*oneSet T x) := by
  let T : Set Ω := {x | f x=d}
  have hT : MeasurableSet T := measurableSet_eq_fun hf measurable_const
  have eqT : f =ᵐ[μ] (fun x => d*oneSet T x) := by
    filter_upwards [he] with x hx
    rcases hx with hx | hx
    · simp [oneSet,T,hx,Ne.symm hd]
    · simp [oneSet,T,hx]
  refine ⟨T,hT,?_,eqT⟩
  have hmass : (∫ x, f x ∂μ)=d*μ.real T := by
    rw [integral_congr_ae eqT,integral_const_mul]
    simp [oneSet,integral_indicator hT]
  exact (mul_left_cancel₀ hd (hmass.symm.trans hi))

/-- Extract the measurable transport set, its exact mass, and support confinement,
from the actual a.e. endpoint-valued transport hypothesis. -/
lemma deterministic_transport (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (d : ℝ) (hd : d ≠ 0) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S)
    (hend : ∀ᵐ x ∂μ, act μ C (oneSet S) x=0 ∨ act μ C (oneSet S) x=d) :
    ∃ T : Set Ω, MeasurableSet T ∧ μ.real T=μ.real S ∧
      (act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet T x)) ∧
      (∀ᵐ p ∂μ.prod μ, 0<C p → oneSet T p.1=oneSet S p.2) := by
  let D := symclip C
  have hD : Measurable D := measurable_symclip hC
  have bD : ∀ p, 0≤D p ∧ D p≤1 := symclip_bounds C
  have eqD : D =ᵐ[μ.prod μ] C := symclip_eq_ae μ C bC sC
  have acteq := act_congr_ae μ D C (oneSet S) eqD
  have rowD : ∀ᵐ x ∂μ, ∫ y, D (x,y) ∂μ=d := by
    filter_upwards [Measure.ae_ae_of_ae_prod eqD,hr] with x hx hrow
    exact (integral_congr_ae hx).trans hrow
  have total : (∫ x, act μ C (oneSet S) x ∂μ)=d*μ.real S := by
    rw [← integral_congr_ae acteq]
    have hh := act_total μ D (oneSet S) hD (oneSet_measurable S hS) bD
      (oneSet_bounds S) (fun x y => symclip_symm C (x,y)) d rowD
    simpa [oneSet,integral_indicator hS] using hh
  obtain ⟨T,hT,hm,he⟩ := endpoint_set μ _
    (measurable_act μ C (oneSet S) hC (oneSet_measurable S hS)) d hd hend _ total
  refine ⟨T,hT,hm,he,?_⟩
  have hde : ∀ᵐ x ∂μ, act μ D (oneSet S) x=d*oneSet T x := acteq.trans he
  have hc := TwoPairBipartiteOrientation.transport_cut_no_crossing μ D hD bD d rowD
    (oneSet S) (oneSet_measurable S hS) (oneSet_binary S)
    (oneSet T) (oneSet_measurable T hT) (oneSet_binary T) hde
  filter_upwards [eqD,hc] with p hp hpc
  rw [← hp]
  exact hpc

lemma act_oneSet_eq_setIntegral (C : Ω × Ω → ℝ) (S : Set Ω)
    (hS : MeasurableSet S) (x : Ω) :
    act μ C (oneSet S) x = ∫ y in S, C (x,y) ∂μ := by
  unfold act
  rw [← integral_indicator hS]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  classical
  by_cases hy : y ∈ S <;> simp [oneSet,hy]

lemma reverse_transport (C : Ω × Ω → ℝ)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (S T : Set Ω)
    (hc : ∀ᵐ p ∂μ.prod μ, 0<C p → oneSet T p.1=oneSet S p.2) :
    act μ C (oneSet T) =ᵐ[μ] (fun x => d*oneSet S x) := by
  have hrev := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  have hp : ∀ᵐ p ∂μ.prod μ, C p*oneSet T p.2=C p*oneSet S p.1 := by
    filter_upwards [bC,sC,hrev] with p hb hs h
    by_cases hz : C p=0
    · simp [hz]
    · have hpos : 0<C (p.2,p.1) := by rw [← hs]; exact lt_of_le_of_ne hb (Ne.symm hz)
      exact congrArg (fun z => C p*z) (h hpos)
  filter_upwards [Measure.ae_ae_of_ae_prod hp,hr] with x hx hrow
  unfold act
  rw [integral_congr_ae hx,integral_mul_const,hrow]

lemma set_transport (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (d : ℝ) (hd : d ≠ 0) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S)
    (hend : ∀ᵐ x ∂μ, (∫ y in S, C (x,y) ∂μ)=0 ∨ (∫ y in S, C (x,y) ∂μ)=d) :
    ∃ T : Set Ω, MeasurableSet T ∧ μ.real T=μ.real S ∧
      (act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet T x)) ∧
      (act μ C (oneSet T) =ᵐ[μ] (fun x => d*oneSet S x)) ∧
      (∀ᵐ p ∂μ.prod μ, 0<C p → oneSet T p.1=oneSet S p.2) := by
  have he : ∀ᵐ x ∂μ, act μ C (oneSet S) x=0 ∨ act μ C (oneSet S) x=d := by
    simpa only [act_oneSet_eq_setIntegral μ C S hS] using hend
  obtain ⟨T,hT,hm,ht,hc⟩ := deterministic_transport μ C hC bC sC d hd hr S hS he
  exact ⟨T,hT,hm,ht,reverse_transport μ C (bC.mono fun _ h => h.1) sC d hr S T hc,hc⟩

end ThirdsDeterministicTransport
end JigBundleModule32

/- Inlined module ThirdsInternalMass; original SHA256 6ee8b990f6c26dc2e29d3b51f34eb7a6b288e3153f04149fe0f27e526761c255 -/
section JigBundleModule33
open MeasureTheory
namespace ThirdsInternalMass
open TwoPairHalfSetOperator ThirdsDeterministicTransport
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma source_target_capacity (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (A B : Set Ω) (hB : MeasurableSet B)
    (hp : ∀ᵐ p ∂μ.prod μ, p.1∈A → 0<C p → p.2∈B) :
    μ.real A=0 ∨ d≤μ.real B := by
  have he : ∀ᵐ x ∂μ, x∈A → d≤μ.real B := by
    filter_upwards [Measure.ae_ae_of_ae_prod bC,Measure.ae_ae_of_ae_prod hp,hr] with x bx px rx
    intro hx
    have hi : Integrable (fun y => C (x,y)) μ :=
      LowSupportAnalysis.unit_integrable_ae (hC.comp (measurable_const.prodMk measurable_id)) bx
    have hle : ∀ᵐ y ∂μ, C (x,y)≤oneSet B y := by
      filter_upwards [bx,px] with y byy pxy
      classical
      by_cases hy : y∈B
      · simpa [oneSet,hy] using byy.2
      · have hh : C (x,y)≤0 := le_of_not_gt (fun hpos => hy (pxy hx hpos))
        simpa [oneSet,hy] using hh
    have hh := integral_mono_ae hi ((integrable_const (1:ℝ)).indicator hB) hle
    simpa [rx,oneSet,integral_indicator hB] using hh
  by_cases hd : d≤μ.real B
  · exact Or.inr hd
  · left
    have hn : ∀ᵐ x ∂μ, x∉A := he.mono (fun _ h hx => hd (h hx))
    have hz : μ A=0 := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hn
    simp [measureReal_def,hz]

lemma internal_mass_dichotomy (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (S T : Set Ω) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hmS : μ.real S=2*d) (hmT : μ.real T=μ.real S)
    (hc : ∀ᵐ p ∂μ.prod μ, 0<C p → oneSet T p.1=oneSet S p.2) :
    μ.real (S∩T)=0 ∨ μ.real (S∩T)=d ∨ μ.real (S∩T)=2*d := by
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  have hi : ∀ᵐ p ∂μ.prod μ, p.1∈S∩T → 0<C p → p.2∈S∩T := by
    filter_upwards [hc,hs,sC] with p hp hq hsym
    intro hx hpos
    have hpos' : 0<C (p.2,p.1) := hsym ▸ hpos
    have hq' := hq hpos'
    have hp' := hp hpos
    classical
    constructor
    · by_contra hy
      simp [oneSet,hx.2,hy] at hp'
    · by_contra hy
      simp [oneSet,hx.1,hy] at hq'
  have hj : ∀ᵐ p ∂μ.prod μ, p.1∈S\T → 0<C p → p.2∈T\S := by
    filter_upwards [hc,hs,sC] with p hp hq hsym
    intro hx hpos
    have hpos' : 0<C (p.2,p.1) := hsym ▸ hpos
    have hq' := hq hpos'
    have hp' := hp hpos
    classical
    constructor
    · by_contra hy
      simp [oneSet,hx.1,hy] at hq'
    · intro hy
      simp [oneSet,hx.2,hy] at hp'
  have bi := source_target_capacity μ C hC bC d hr (S∩T) (S∩T) (hS.inter hT) hi
  have bj := source_target_capacity μ C hC bC d hr (S\T) (T\S) (hT.diff hS) hj
  have eS : μ.real (S∩T)+μ.real (S\T)=μ.real S := measureReal_inter_add_sdiff₀ hT.nullMeasurableSet
  have eT : μ.real (S∩T)+μ.real (T\S)=μ.real T := by
    simpa only [Set.inter_comm] using (measureReal_inter_add_sdiff₀ (μ := μ) (s := T) hS.nullMeasurableSet)
  rcases bi with hz | hi
  · exact Or.inl hz
  · rcases bj with hz | hj
    · right; right; linarith
    · right; left; linarith
end ThirdsInternalMass
end JigBundleModule33

/- Inlined module ThirdsInternalSaturation; original SHA256 2f2b50a8d00a228304931b1d043e115986e59ecfe4c8275f8a01ea3c43a5829e -/
section JigBundleModule34
open MeasureTheory
namespace ThirdsInternalSaturation
open TwoPairHalfSetOperator ThirdsDeterministicTransport ThirdsInternalMass
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma supported_mass_saturation (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p≤1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (I : Set Ω) (hI : MeasurableSet I) (hm : μ.real I=d)
    (hp : ∀ᵐ p ∂μ.prod μ, p.1∈I → 0<C p → p.2∈I) :
    ∀ᵐ p ∂μ.prod μ, p.1∈I → C p=oneSet I p.2 := by
  have hmeas : MeasurableSet {p : Ω × Ω | p.1∈I → C p=oneSet I p.2} :=
    (hI.preimage measurable_fst).imp
      (measurableSet_eq_fun hC ((oneSet_measurable I hI).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod bC,Measure.ae_ae_of_ae_prod hp,hr] with x bx px rx
  by_cases hx : x∈I
  · have hiC : Integrable (fun y => C (x,y)) μ :=
      LowSupportAnalysis.unit_integrable_ae (hC.comp (measurable_const.prodMk measurable_id)) bx
    have hiI : Integrable (oneSet I) μ := (integrable_const (1:ℝ)).indicator hI
    have hle : ∀ᵐ y ∂μ, C (x,y)≤oneSet I y := by
      filter_upwards [bx,px] with y byy pxy
      classical
      by_cases hy : y∈I
      · simpa [oneSet,hy] using byy.2
      · have hz : C (x,y)≤0 := le_of_not_gt (fun hh => hy (pxy hx hh))
        simpa [oneSet,hy] using hz
    have hz : (∫ y, oneSet I y-C (x,y) ∂μ)=0 := by
      rw [integral_sub hiI hiC,rx]
      simp [oneSet,integral_indicator hI,hm]
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (hle.mono fun _ h => sub_nonneg.mpr h) (hiI.sub hiC)).mp hz
    filter_upwards [he] with y hy
    intro _
    exact (sub_eq_zero.mp hy).symm
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hx h))

lemma internal_transport_and_clique (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p≤1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (d : ℝ) (hd : d≠0) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ᵐ x ∂μ, (∫ y in S, C (x,y) ∂μ)=0 ∨ (∫ y in S, C (x,y) ∂μ)=d) :
    ∃ T : Set Ω, MeasurableSet T ∧ μ.real T=μ.real S ∧
      (act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet T x)) ∧
      (act μ C (oneSet T) =ᵐ[μ] (fun x => d*oneSet S x)) ∧
      (μ.real (S∩T)=0 ∨ μ.real (S∩T)=d ∨ μ.real (S∩T)=2*d) ∧
      (μ.real (S∩T)=d → ∀ᵐ p ∂μ.prod μ, p.1∈S∩T → C p=oneSet (S∩T) p.2) := by
  obtain ⟨T,hT,hmT,hforward,hback,hc⟩ := set_transport μ C hC bC sC d hd hr S hS hend
  refine ⟨T,hT,hmT,hforward,hback,internal_mass_dichotomy μ C hC bC sC d hr S T hS hT hmS hmT hc,?_⟩
  intro hm
  apply supported_mass_saturation μ C hC bC d hr (S∩T) (hS.inter hT) hm
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  filter_upwards [hc,hs,sC] with p hp hq hsym
  intro hx hpos
  have hpos' : 0<C (p.2,p.1) := hsym ▸ hpos
  have hq' := hq hpos'
  have hp' := hp hpos
  classical
  constructor
  · by_contra hy
    simp [oneSet,hx.2,hy] at hp'
  · by_contra hy
    simp [oneSet,hx.1,hy] at hq'
end ThirdsInternalSaturation
end JigBundleModule34

/- Inlined module ThirdsInternalCount; original SHA256 323f77be79b47f203c6d9b036a87475208132c6e7c47a0f4b223f896c4402d8b -/
section JigBundleModule35
open MeasureTheory
open scoped BigOperators
namespace ThirdsInternalCount
open TwoPairHalfSetOperator ThirdsDeterministicTransport
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma internal_count (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : d≠0)
    (hm : μ.real S=2*d) (T : Fin 6 → Set Ω)
    (hact : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T c) x)) :
    ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=2 := by
  have hb : ∀ᵐ x ∂μ, ∀ c, ∀ᵐ y ∂μ, 0≤W c (x,y) ∧ W c (x,y)≤1 := by
    exact (ae_all_iff.mpr fun c => Measure.ae_ae_of_ae_prod (bW c))
  have ha : ∀ᵐ x ∂μ, ∀ c, act μ (W c) (oneSet S) x=d*oneSet (T c) x := ae_all_iff.mpr hact
  filter_upwards [hb,ha,Measure.ae_ae_of_ae_prod hpart] with x bx ax px
  have hi (c : Fin 6) : Integrable (fun y => W c (x,y)*oneSet S y) μ := by
    apply LowSupportAnalysis.unit_integrable_ae
      ((hW c).comp (measurable_const.prodMk measurable_id) |>.mul (oneSet_measurable S hS))
    filter_upwards [bx c] with y hy
    exact LowSupportAnalysis.mul_unit hy (oneSet_bounds S y)
  have hs : (∑ c, act μ (W c) (oneSet S) x)=μ.real S := by
    unfold act
    rw [← integral_finset_sum Finset.univ (fun c _ => hi c)]
    have he : (fun y => ∑ c, W c (x,y)*oneSet S y) =ᵐ[μ] oneSet S := by
      filter_upwards [px] with y hy
      rw [← Finset.sum_mul,hy,one_mul]
    rw [integral_congr_ae he]
    simp [oneSet,integral_indicator hS]
  simp_rw [ax] at hs
  rw [← Finset.mul_sum,hm] at hs
  exact mul_left_cancel₀ hd (by simpa [mul_comm] using hs)

lemma square_null (A : Set Ω)
    (h : ∀ᵐ p ∂μ.prod μ, ¬(p.1∈A ∧ p.2∈A)) : μ.real A=0 := by
  have hz : (μ.prod μ) (A ×ˢ A)=0 := by
    change (μ.prod μ) {p | p.1∈A ∧ p.2∈A}=0
    simpa only [ae_iff,not_not] using h
  rw [Measure.prod_prod] at hz
  have hA : μ A=0 := (mul_eq_zero.mp hz).elim id id
  simp [measureReal_def,hA]

lemma full_cliques_disjoint (C D : Ω × Ω → ℝ) (I J : Set Ω)
    (hcap : ∀ᵐ p ∂μ.prod μ, C p+D p≤1)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1∈I → C p=oneSet I p.2)
    (hJ : ∀ᵐ p ∂μ.prod μ, p.1∈J → D p=oneSet J p.2) :
    μ.real (I∩J)=0 := by
  apply square_null μ (I∩J)
  filter_upwards [hcap,hI,hJ] with p hp hi hj
  intro h
  have hc := hi h.1.1
  have hd := hj h.1.2
  classical
  simp only [oneSet,Set.indicator_of_mem h.2.1] at hc
  simp only [oneSet,Set.indicator_of_mem h.2.2] at hd
  linarith

lemma distinct_color_cliques_disjoint (W : Fin 6 → Ω × Ω → ℝ)
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (c e : Fin 6) (hne : c≠e) (I J : Set Ω)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1∈I → W c p=oneSet I p.2)
    (hJ : ∀ᵐ p ∂μ.prod μ, p.1∈J → W e p=oneSet J p.2) :
    μ.real (I∩J)=0 := by
  apply full_cliques_disjoint μ (W c) (W e) I J ?_ hI hJ
  have hb : ∀ᵐ p ∂μ.prod μ, ∀ i, 0≤W i p := ae_all_iff.mpr bW
  filter_upwards [hb,hpart] with p hp hsum
  have hh : (∑ i ∈ ({c,e} : Finset (Fin 6)), W i p) ≤ ∑ i, W i p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)
  simpa [Finset.sum_pair hne,hsum] using hh
end ThirdsInternalCount
end JigBundleModule35

/- Inlined module ThirdsArrangementCounts; original SHA256 268829b91035223cdabd6f46d7d22183afd5a4d6decbdcd8c1fb1effaaa8b1c9 -/
section JigBundleModule36
open MeasureTheory
open scoped BigOperators Classical
namespace ThirdsArrangementCounts
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma three_disjoint_halves_impossible (S A B C : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (aS : A⊆S) (bS : B⊆S) (cS : C⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d)
    (mA : μ.real A=d) (mB : μ.real B=d) (mC : μ.real C=d)
    (ab : μ.real (A∩B)=0) (ac : μ.real (A∩C)=0) (bc : μ.real (B∩C)=0) : False := by
  have eAB := measureReal_union_add_inter₀ (μ := μ) (s := A) hB.nullMeasurableSet
  have z : μ.real ((A∪B)∩C)=0 := by
    rw [Set.union_inter_distrib_right]
    exact measureReal_union_null ac bc
  have eABC := measureReal_union_add_inter₀ (μ := μ) (s := A∪B) hC.nullMeasurableSet
  have hsub : (A∪B)∪C ⊆ S := Set.union_subset (Set.union_subset aS bS) cS
  have hle := measureReal_mono (μ := μ) hsub
  linarith

lemma partial_card_le_two (S : Set Ω) (I : Fin 6 → Set Ω)
    (hI : ∀ i, MeasurableSet (I i)) (hsub : ∀ i, I i⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d)
    (hdisj : ∀ i j, i≠j → μ.real (I i)=d → μ.real (I j)=d → μ.real (I i∩I j)=0) :
    (Finset.univ.filter (fun i => μ.real (I i)=d)).card≤2 := by
  classical
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge hn)
  have ma : μ.real (I a)=d := (Finset.mem_filter.mp ha).2
  have mb : μ.real (I b)=d := (Finset.mem_filter.mp hb).2
  have mc : μ.real (I c)=d := (Finset.mem_filter.mp hc).2
  exact three_disjoint_halves_impossible μ S (I a) (I b) (I c) (hI a) (hI b) (hI c)
    (hsub a) (hsub b) (hsub c) d hd mS ma mb mc
    (hdisj a b hab ma mb) (hdisj a c hac ma mc) (hdisj b c hbc mb mc)

lemma mass_count_alternatives (m : Fin 6 → ℝ) (d : ℝ) (hd : 0<d)
    (hm : ∀ i, m i=0 ∨ m i=d ∨ m i=2*d)
    (hs : ∑ i, m i=4*d)
    (hp : (Finset.univ.filter (fun i => m i=d)).card≤2) :
    ((Finset.univ.filter (fun i => m i=2*d)).card=2 ∧
      (Finset.univ.filter (fun i => m i=d)).card=0) ∨
    ((Finset.univ.filter (fun i => m i=2*d)).card=1 ∧
      (Finset.univ.filter (fun i => m i=d)).card=2) := by
  classical
  have he : ∀ i, m i=(if m i=d then d else 0)+(if m i=2*d then 2*d else 0) := by
    intro i
    rcases hm i with h | h | h
    · simp [h,ne_of_lt hd,ne_of_gt hd,show (0:ℝ)≠2*d by linarith]
    · simp [h,show d≠2*d by linarith]
    · simp [h,show 2*d≠d by linarith]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => he i)
  simp only [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul] at hsum
  have heq : 2*(Finset.univ.filter (fun i => m i=2*d)).card+
      (Finset.univ.filter (fun i => m i=d)).card=4 := by
    have hh : (2*(Finset.univ.filter (fun i => m i=2*d)).card+
      (Finset.univ.filter (fun i => m i=d)).card : ℝ)=4 := by nlinarith
    exact_mod_cast hh
  omega
end ThirdsArrangementCounts
end JigBundleModule36

/- Inlined module ThirdsArrangementLabels; original SHA256 d26f16cfc950393630a1f4579f33fba594498428cf0ddffd06b9854377834afb -/
section JigBundleModule37
open scoped BigOperators Classical
namespace ThirdsArrangementLabels
lemma labels (m : Fin 6 → ℝ) (d : ℝ) (hd : 0<d)
    (hm : ∀ i, m i=0 ∨ m i=d ∨ m i=2*d)
    (hcase : ((Finset.univ.filter (fun i => m i=2*d)).card=2 ∧
        (Finset.univ.filter (fun i => m i=d)).card=0) ∨
      ((Finset.univ.filter (fun i => m i=2*d)).card=1 ∧
        (Finset.univ.filter (fun i => m i=d)).card=2)) :
    (∃ a b : Fin 6, a≠b ∧ m a=2*d ∧ m b=2*d ∧
      ∀ i, i≠a → i≠b → m i=0) ∨
    (∃ a b g : Fin 6, a≠b ∧ a≠g ∧ b≠g ∧ m a=d ∧ m b=d ∧ m g=2*d ∧
      ∀ i, i≠a → i≠b → i≠g → m i=0) := by
  let G := Finset.univ.filter (fun i => m i=2*d)
  let P := Finset.univ.filter (fun i => m i=d)
  have mg (i) : i∈G ↔ m i=2*d := by simp [G]
  have mp (i) : i∈P ↔ m i=d := by simp [P]
  rcases hcase with ⟨hg,hp⟩ | ⟨hg,hp⟩
  · obtain ⟨a,b,ab,hab⟩ := Finset.card_eq_two.mp hg
    have ma : m a=2*d := (mg a).mp (by change a∈Finset.univ.filter _; rw [hab]; simp)
    have mb : m b=2*d := (mg b).mp (by change b∈Finset.univ.filter _; rw [hab]; simp)
    refine Or.inl ⟨a,b,ab,ma,mb,?_⟩
    intro i ia ib
    rcases hm i with h | h | h
    · exact h
    · have hi := (mp i).mpr h
      have he : P=∅ := Finset.card_eq_zero.mp hp
      exfalso
      simpa [he] using hi
    · have hi := (mg i).mpr h
      change i∈Finset.univ.filter _ at hi
      exfalso
      simpa [hab,ia,ib] using hi
  · obtain ⟨g,hgset⟩ := Finset.card_eq_one.mp hg
    obtain ⟨a,b,ab,hab⟩ := Finset.card_eq_two.mp hp
    have ma : m a=d := (mp a).mp (by change a∈Finset.univ.filter _; rw [hab]; simp)
    have mb : m b=d := (mp b).mp (by change b∈Finset.univ.filter _; rw [hab]; simp)
    have mgg : m g=2*d := (mg g).mp (by change g∈Finset.univ.filter _; rw [hgset]; simp)
    have ag : a≠g := by intro h; rw [h] at ma; linarith
    have bg : b≠g := by intro h; rw [h] at mb; linarith
    refine Or.inr ⟨a,b,g,ab,ag,bg,ma,mb,mgg,?_⟩
    intro i ia ib ig
    rcases hm i with h | h | h
    · exact h
    · have hi := (mp i).mpr h
      change i∈Finset.univ.filter _ at hi
      exfalso
      simpa [hab,ia,ib] using hi
    · have hi := (mg i).mpr h
      change i∈Finset.univ.filter _ at hi
      exfalso
      simpa [hgset,ig] using hi
end ThirdsArrangementLabels
end JigBundleModule37

/- Inlined module ThirdsInternalArrangement; original SHA256 9c504a85a9025aecdb70a83f7fc6e131ca38eddb6e1b6832750473f6156a6be8 -/
section JigBundleModule38
open MeasureTheory
open scoped BigOperators Classical
namespace ThirdsInternalArrangement
open TwoPairHalfSetOperator ThirdsInternalSaturation ThirdsInternalCount ThirdsArrangementCounts
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma internal_mass_sum (S : Set Ω) (hS : MeasurableSet S)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hc : ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=2) :
    (∑ c, μ.real (S∩T c))=2*μ.real S := by
  have hi (c : Fin 6) : Integrable (oneSet (S∩T c)) μ :=
    (integrable_const (1:ℝ)).indicator (hS.inter (hT c))
  have hm (c : Fin 6) : (∫ x, oneSet (S∩T c) x ∂μ)=μ.real (S∩T c) := by
    simp [oneSet,integral_indicator (hS.inter (hT c))]
  have he : (fun x => ∑ c, oneSet (S∩T c) x) =ᵐ[μ] (fun x => 2*oneSet S x) := by
    filter_upwards [hc] with x hx
    by_cases hs : x∈S
    · have hh (c : Fin 6) : oneSet (S∩T c) x=oneSet (T c) x := by
        by_cases ht : x∈T c <;> simp [oneSet,hs,ht]
      simp_rw [hh]
      simpa [oneSet,hs] using hx
    · simp [oneSet,hs]
  calc
    _ = ∑ c, ∫ x, oneSet (S∩T c) x ∂μ := by simp_rw [hm]
    _ = ∫ x, ∑ c, oneSet (S∩T c) x ∂μ := (integral_finset_sum _ (fun c _ => hi c)).symm
    _ = ∫ x, 2*oneSet S x ∂μ := integral_congr_ae he
    _ = _ := by rw [integral_const_mul]; simp [oneSet,integral_indicator hS]

/-- The two possible internal color arrangements, derived from the actual
six kernels and their deterministic transport hypothesis. -/
lemma arrangement_counts (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0<d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d) :
    ∃ T : Fin 6 → Set Ω, (∀ c, MeasurableSet (T c)) ∧
      (∀ c, μ.real (T c)=μ.real S) ∧
      (∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T c) x)) ∧
      (∀ c, μ.real (S∩T c)=0 ∨ μ.real (S∩T c)=d ∨ μ.real (S∩T c)=2*d) ∧
      (∀ c, μ.real (S∩T c)=d → ∀ᵐ p ∂μ.prod μ,
        p.1∈S∩T c → W c p=oneSet (S∩T c) p.2) ∧
      (((Finset.univ.filter (fun c => μ.real (S∩T c)=2*d)).card=2 ∧
        (Finset.univ.filter (fun c => μ.real (S∩T c)=d)).card=0) ∨
       ((Finset.univ.filter (fun c => μ.real (S∩T c)=2*d)).card=1 ∧
        (Finset.univ.filter (fun c => μ.real (S∩T c)=d)).card=2)) := by
  have hall := fun c => internal_transport_and_clique μ (W c) (hW c) (bW c) (sW c)
    d (ne_of_gt hd) (hr c) S hS hmS (hend c)
  choose T hT hmT hf hb hm hclique using hall
  have hc := internal_count μ W hW bW hpart S hS d (ne_of_gt hd) hmS T hf
  have hsum : (∑ c, μ.real (S∩T c))=4*d := by
    rw [internal_mass_sum μ S hS T hT hc,hmS]; ring
  have hp := partial_card_le_two μ S (fun c => S∩T c) (fun c => hS.inter (hT c))
    (fun _ => Set.inter_subset_left) d hd hmS (by
      intro c e hne hmc hme
      exact distinct_color_cliques_disjoint μ W (fun i => (bW i).mono fun _ h => h.1)
        hpart c e hne (S∩T c) (S∩T e) (hclique c hmc) (hclique e hme))
  exact ⟨T,hT,hmT,hf,hm,hclique,mass_count_alternatives (fun c => μ.real (S∩T c)) d hd hm hsum hp⟩
end ThirdsInternalArrangement
end JigBundleModule38

/- Inlined module ThirdsLiteralLayout; original SHA256 402e89483d03a26e4cdbcb1173530b942256143bb803f104327407b89ac89946 -/
section JigBundleModule39
open MeasureTheory
open scoped BigOperators Classical
namespace ThirdsLiteralLayout
open TwoPairHalfSetOperator ThirdsDeterministicTransport
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma null_indicator (A : Set Ω) (hm : μ.real A=0) : oneSet A =ᵐ[μ] (fun _ => 0) := by
  have hz : μ A=0 := (measureReal_eq_zero_iff).mp hm
  have hn : ∀ᵐ x ∂μ, x∉A := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hz
  filter_upwards [hn] with x hx
  simp [oneSet,hx]

lemma full_subset_indicator (A S : Set Ω) (hA : MeasurableSet A)
    (hsub : A⊆S) (hm : μ.real A=μ.real S) : oneSet A =ᵐ[μ] oneSet S := by
  have hh := measureReal_inter_add_sdiff₀ (μ := μ) (s := S) hA.nullMeasurableSet
  have he : S∩A=A := Set.inter_eq_right.mpr hsub
  rw [he,hm] at hh
  have hz : μ.real (S\A)=0 := by linarith
  have hn : ∀ᵐ x ∂μ, x∉S\A := by
    have hzero := (measureReal_eq_zero_iff).mp hz
    simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hzero
  filter_upwards [hn] with x hx
  by_cases ha : x∈A
  · simp [oneSet,ha,hsub ha]
  · have hs : x∉S := fun hs => hx ⟨hs,ha⟩
    simp [oneSet,ha,hs]

lemma two_halves_cover (X Y S : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hx : X⊆S) (hy : Y⊆S) (d : ℝ)
    (mx : μ.real X=d) (my : μ.real Y=d) (ms : μ.real S=2*d)
    (hdis : μ.real (X∩Y)=0) : oneSet (X∪Y) =ᵐ[μ] oneSet S := by
  apply full_subset_indicator μ (X∪Y) S (hX.union hY) (Set.union_subset hx hy)
  have h := measureReal_union_add_inter₀ (μ := μ) (s := X) hY.nullMeasurableSet
  linarith

lemma zero_internal_kernel (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p≤1)
    (S T : Set Ω) (hS : MeasurableSet S) (d : ℝ)
    (ha : act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet T x))
    (hm : μ.real (S∩T)=0) :
    ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → C p=0 := by
  have hn : ∀ᵐ x ∂μ, x∉S∩T := by
    have hz := (measureReal_eq_zero_iff).mp hm
    simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hz
  have hmeas : MeasurableSet {p : Ω × Ω | p.1∈S → p.2∈S → C p=0} :=
    (hS.preimage measurable_fst).imp ((hS.preimage measurable_snd).imp
      (measurableSet_eq_fun hC measurable_const))
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod bC,ha,hn] with x bx ax nx
  by_cases hx : x∈S
  · have nt : x∉T := fun ht => nx ⟨hx,ht⟩
    have hz : (∫ y, C (x,y)*oneSet S y ∂μ)=0 := by
      simpa [act,oneSet,nt] using ax
    have hi : Integrable (fun y => C (x,y)*oneSet S y) μ := by
      apply LowSupportAnalysis.unit_integrable_ae
        (((hC.comp (measurable_const.prodMk measurable_id))).mul (oneSet_measurable S hS))
      filter_upwards [bx] with y hy
      exact LowSupportAnalysis.mul_unit hy (oneSet_bounds S y)
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (bx.mono fun y hy => mul_nonneg hy.1 (oneSet_bounds S y).1) hi).mp hz
    filter_upwards [he] with y hy
    intro _ hys
    simpa [oneSet,hys] using hy
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hx h))

lemma unique_global_cross (W : Fin 6 → Ω × Ω → ℝ)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (a b g : Fin 6) (ab : a≠b) (ag : a≠g) (bg : b≠g)
    (X Y S : Set Ω) (xs : X⊆S) (ys : Y⊆S)
    (hdis : μ.real (X∩Y)=0)
    (ha : ∀ᵐ p ∂μ.prod μ, p.1∈X → W a p=oneSet X p.2)
    (hb : ∀ᵐ p ∂μ.prod μ, p.1∈Y → W b p=oneSet Y p.2)
    (hz : ∀ c, c≠a → c≠b → c≠g → ∀ᵐ p ∂μ.prod μ,
      p.1∈S → p.2∈S → W c p=0) :
    ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Y → W g p=1 := by
  have hn : ∀ᵐ x ∂μ, x∉X∩Y := by
    have hh := (measureReal_eq_zero_iff).mp hdis
    simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hh
  have hleft := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hn
  have hright := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hn
  have hbs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hb
  have hall : ∀ᵐ p ∂μ.prod μ, ∀ c, c≠a → c≠b → c≠g → p.1∈S → p.2∈S → W c p=0 := by
    apply ae_all_iff.mpr
    intro c
    by_cases ca : c=a
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h ca))
    by_cases cb : c=b
    · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h cb))
    by_cases cg : c=g
    · exact Filter.Eventually.of_forall (fun _ _ _ h => False.elim (h cg))
    exact (hz c ca cb cg).mono (fun _ h _ _ _ => h)
  filter_upwards [hpart,ha,hbs,sW b,hleft,hright,hall] with p hp hpa hpb hsym nl nr hzero
  intro px py
  have nx : p.1∉Y := fun h => nl ⟨px,h⟩
  have ny : p.2∉X := fun h => nr ⟨h,py⟩
  have ea : W a p=0 := by simpa [oneSet,ny] using hpa px
  have eb : W b p=0 := by
    have hh := hpb py
    change W b (p.2,p.1)=oneSet Y p.1 at hh
    simpa [oneSet,nx,← hsym] using hh
  have he : ∀ c, c≠g → W c p=0 := by
    intro c cg
    by_cases ca : c=a
    · simpa [ca] using ea
    by_cases cb : c=b
    · simpa [cb] using eb
    exact hzero c ca cb cg (xs px) (ys py)
  have hsum : (∑ c, W c p)=W g p := Finset.sum_eq_single g
    (fun c _ hc => he c hc) (fun h => False.elim (h (Finset.mem_univ _)))
  exact hsum.symm.trans hp
end ThirdsLiteralLayout
end JigBundleModule39

/- Inlined module ThirdsLayoutCoupling; original SHA256 f6b8978d4e892fc2aedcd51941d7222b921714acf65277b56de43fc6945ddac8 -/
section JigBundleModule40
open MeasureTheory
open scoped BigOperators Classical
namespace ThirdsLayoutCoupling
open TwoPairHalfSetOperator ThirdsLiteralLayout ThirdsInternalCount
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma full_rectangle_rows (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p≤1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (X Y : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y) (mY : μ.real Y=d)
    (hc : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Y → C p=1) :
    ∀ᵐ p ∂μ.prod μ, p.1∈X → C p=oneSet Y p.2 := by
  have hm : MeasurableSet {p : Ω × Ω | p.1∈X → C p=oneSet Y p.2} :=
    (hX.preimage measurable_fst).imp
      (measurableSet_eq_fun hC ((oneSet_measurable Y hY).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod bC,Measure.ae_ae_of_ae_prod hc,hr] with x bx cx rx
  by_cases hx : x∈X
  · have hiC := LowSupportAnalysis.unit_integrable_ae
      (hC.comp (measurable_const.prodMk measurable_id)) bx
    have hiY : Integrable (oneSet Y) μ := (integrable_const (1:ℝ)).indicator hY
    have hle : oneSet Y ≤ᵐ[μ] (fun y => C (x,y)) := by
      filter_upwards [bx,cx] with y hy cy
      by_cases hys : y∈Y
      · simp [oneSet,hys,cy hx hys]
      · simpa [oneSet,hys] using hy.1
    have he : (∫ y, oneSet Y y ∂μ)=(∫ y, C (x,y) ∂μ) := by
      simp [oneSet,integral_indicator hY,mY,rx]
    have hz := (integral_eq_iff_of_ae_le hiY hiC hle).mp he
    exact hz.mono (fun y hy _ => hy.symm)
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hx h))

/-- The one-global/two-partial branch has the literal complete bipartite
kernel for its global internal color. All other data are proved transport outputs. -/
lemma three_label_layout (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hact : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T c) x))
    (a b g : Fin 6) (ab : a≠b) (ag : a≠g) (bg : b≠g)
    (ma : μ.real (S∩T a)=d) (mb : μ.real (S∩T b)=d)
    (hz : ∀ c, c≠a → c≠b → c≠g → μ.real (S∩T c)=0)
    (ha : ∀ᵐ p ∂μ.prod μ, p.1∈S∩T a → W a p=oneSet (S∩T a) p.2)
    (hb : ∀ᵐ p ∂μ.prod μ, p.1∈S∩T b → W b p=oneSet (S∩T b) p.2) :
    (oneSet ((S∩T a)∪(S∩T b)) =ᵐ[μ] oneSet S) ∧
    μ.real ((S∩T a)∩(S∩T b))=0 ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈S∩T a → W g p=oneSet (S∩T b) p.2) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈S∩T b → W g p=oneSet (S∩T a) p.2) := by
  have hdis := distinct_color_cliques_disjoint μ W
    (fun c => (bW c).mono fun _ h => h.1) hpart a b ab (S∩T a) (S∩T b) ha hb
  have hzero : ∀ c, c≠a → c≠b → c≠g → ∀ᵐ p ∂μ.prod μ,
      p.1∈S → p.2∈S → W c p=0 := by
    intro c ca cb cg
    exact zero_internal_kernel μ (W c) (hW c) (bW c) S (T c) hS d (hact c) (hz c ca cb cg)
  have hcross := unique_global_cross μ W hpart sW a b g ab ag bg
    (S∩T a) (S∩T b) S Set.inter_subset_left Set.inter_subset_left hdis ha hb hzero
  have hcross' : ∀ᵐ p ∂μ.prod μ, p.1∈S∩T b → p.2∈S∩T a → W g p=1 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae hcross,sW g] with p hp hs
    intro hx hy
    exact hs.trans (hp hy hx)
  refine ⟨two_halves_cover μ (S∩T a) (S∩T b) S (hS.inter (hT a)) (hS.inter (hT b))
    Set.inter_subset_left Set.inter_subset_left d ma mb mS hdis,hdis,?_,?_⟩
  · exact full_rectangle_rows μ (W g) (hW g) (bW g) d (hr g)
      (S∩T a) (S∩T b) (hS.inter (hT a)) (hS.inter (hT b)) mb hcross
  · exact full_rectangle_rows μ (W g) (hW g) (bW g) d (hr g)
      (S∩T b) (S∩T a) (hS.inter (hT b)) (hS.inter (hT a)) ma hcross'
end ThirdsLayoutCoupling
end JigBundleModule40

/- Inlined module ThirdsStartingDichotomy; original SHA256 b1be030dcf75676c19694b864a6c63154e033f7e0c540ee585fbdeb9c45edc10 -/
section JigBundleModule41
open MeasureTheory
open scoped BigOperators Classical
namespace ThirdsStartingDichotomy
open TwoPairHalfSetOperator ThirdsLiteralLayout ThirdsInternalArrangement ThirdsLayoutCoupling
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma global_internal_act (C : Ω × Ω → ℝ) (S T : Set Ω)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (d : ℝ)
    (hm : μ.real (S∩T)=μ.real S)
    (ha : act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet T x)) :
    ∀ᵐ x ∂μ, x∈S → act μ C (oneSet S) x=d := by
  have he := full_subset_indicator μ (S∩T) S (hS.inter hT) Set.inter_subset_left hm
  filter_upwards [he,ha] with x hx hax
  intro xs
  have xt : x∈T := by
    by_contra hn
    simp [oneSet,xs,hn] at hx
  simpa [oneSet,xt] using hax

lemma two_color_sum (W : Fin 6 → Ω × Ω → ℝ) (S : Set Ω)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (a b : Fin 6) (ab : a≠b)
    (hz : ∀ c, c≠a → c≠b → ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W c p=0) :
    ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W a p+W b p=1 := by
  have hall : ∀ᵐ p ∂μ.prod μ, ∀ c, c≠a → c≠b → p.1∈S → p.2∈S → W c p=0 := by
    apply ae_all_iff.mpr
    intro c
    by_cases ca : c=a
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h ca))
    by_cases cb : c=b
    · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h cb))
    exact (hz c ca cb).mono (fun _ h _ _ => h)
  filter_upwards [hpart,hall] with p hp h
  intro xs ys
  have he : (∑ i ∈ Finset.univ.erase a, W i p)=W b p := by
    apply Finset.sum_eq_single b
    · intro i hi ib
      exact h i (Finset.mem_erase.mp hi).1 ib xs ys
    · intro hb
      exfalso
      apply hb
      simp [Ne.symm ab]
  have hs := Finset.sum_erase_add (s := Finset.univ) (f := fun i => W i p) (Finset.mem_univ a)
  rw [he,hp] at hs
  linarith

lemma starting_dichotomy (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0<d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d) :
    (∃ a b : Fin 6, a≠b ∧
      (∀ᵐ x ∂μ, x∈S → act μ (W a) (oneSet S) x=d) ∧
      (∀ᵐ x ∂μ, x∈S → act μ (W b) (oneSet S) x=d) ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W a p+W b p=1) ∧
      (∀ c, c≠a → c≠b → ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W c p=0)) ∨
    (∃ a b g : Fin 6, ∃ X Y : Set Ω, a≠b ∧ a≠g ∧ b≠g ∧
      MeasurableSet X ∧ MeasurableSet Y ∧ X⊆S ∧ Y⊆S ∧
      μ.real X=d ∧ μ.real Y=d ∧ μ.real (X∩Y)=0 ∧
      (oneSet (X∪Y) =ᵐ[μ] oneSet S) ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈X → W a p=oneSet X p.2) ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈Y → W b p=oneSet Y p.2) ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈X → W g p=oneSet Y p.2) ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈Y → W g p=oneSet X p.2)) := by
  obtain ⟨T,hT,hmT,ha,hm,hclique,hcases⟩ := arrangement_counts μ W hW bW sW hpart d hd hr S hS mS hend
  rcases ThirdsArrangementLabels.labels (fun c => μ.real (S∩T c)) d hd hm hcases with h | h
  · obtain ⟨a,b,ab,ma,mb,hzero⟩ := h
    have hz : ∀ c, c≠a → c≠b → ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W c p=0 := by
      intro c ca cb
      exact zero_internal_kernel μ (W c) (hW c) (bW c) S (T c) hS d (ha c) (hzero c ca cb)
    exact Or.inl ⟨a,b,ab,global_internal_act μ (W a) S (T a) hS (hT a) d (ma.trans mS.symm) (ha a),
      global_internal_act μ (W b) S (T b) hS (hT b) d (mb.trans mS.symm) (ha b),
      two_color_sum μ W S hpart a b ab hz,hz⟩
  · obtain ⟨a,b,g,ab,ag,bg,ma,mb,mg,hzero⟩ := h
    have hl := three_label_layout μ W hW bW sW hpart d hr S hS mS T hT ha a b g ab ag bg ma mb hzero
      (hclique a ma) (hclique b mb)
    exact Or.inr ⟨a,b,g,S∩T a,S∩T b,ab,ag,bg,hS.inter (hT a),hS.inter (hT b),
      Set.inter_subset_left,Set.inter_subset_left,ma,mb,hl.2.1,hl.1,hclique a ma,hclique b mb,hl.2.2.1,hl.2.2.2⟩
end ThirdsStartingDichotomy
end JigBundleModule41

/- Inlined module ThirdsNormalizedRestriction; original SHA256 4a578e06e8874ab525a7fd0e16d0f99a19e8282ee0d85b683a290d2cc79db9ca -/
section JigBundleModule42
open MeasureTheory
namespace ThirdsNormalizedRestriction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma conditional_integral (S : Set Ω) (f : Ω → ℝ) :
    (∫ x, f x ∂ProbabilityTheory.cond μ S)=(μ.real S)⁻¹*(∫ x in S, f x ∂μ) := by
  simp only [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,
    measureReal_def,smul_eq_mul]
lemma conditional_ae (S : Set Ω) (hS : MeasurableSet S) (P : Ω → Prop)
    (hP : ∀ᵐ x ∂μ, x ∈ S → P x) : ∀ᵐ x ∂ProbabilityTheory.cond μ S, P x := by
  exact Measure.ae_smul_measure ((ae_restrict_iff' hS).mpr hP) _
lemma conditional_row_half (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0<d)
    (hm : μ.real S=2*d) (C : Ω × Ω → ℝ)
    (hr : ∀ᵐ x ∂μ, x ∈ S → (∫ y in S, C (x,y) ∂μ)=d) :
    ∀ᵐ x ∂ProbabilityTheory.cond μ S, (∫ y, C (x,y) ∂ProbabilityTheory.cond μ S)=(1:ℝ)/2 := by
  apply conditional_ae μ S hS
  filter_upwards [hr] with x hx
  intro hxs
  rw [conditional_integral μ S,hm,hx hxs]
  field_simp
  <;> nlinarith
lemma conditional_probability (S : Set Ω) (d : ℝ) (hd : 0<d) (hm : μ.real S=2*d) :
    IsProbabilityMeasure (ProbabilityTheory.cond μ S) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  intro hz
  have hh : μ.real S=0 := by simp [measureReal_def,hz]
  linarith
lemma conditional_cycle4 (S : Set Ω) (f g h k : Ω × Ω → ℝ) :
    Submissions.E811FourColorParity.Representatives.cycle4 (ProbabilityTheory.cond μ S) f g h k =
      (μ.real S)⁻¹^4 * (∫ x in S, ∫ y in S, ∫ z in S, ∫ t in S,
        f (x,y)*g (y,z)*h (z,t)*k (t,x) ∂μ ∂μ ∂μ ∂μ) := by
  unfold Submissions.E811FourColorParity.Representatives.cycle4
  simp_rw [conditional_integral,integral_const_mul]
  ring
lemma conditional_real (S X : Set Ω) (hX : MeasurableSet X) :
    (ProbabilityTheory.cond μ S).real X=(μ.real S)⁻¹*μ.real (X ∩ S) := by
  simp only [measureReal_def,ProbabilityTheory.cond,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply hX,ENNReal.toReal_mul,ENNReal.toReal_inv]
lemma ambient_half_mass (S X : Set Ω) (hX : MeasurableSet X) (d : ℝ) (hd : 0<d)
    (hm : μ.real S=2*d) (hhalf : (ProbabilityTheory.cond μ S).real X=(1:ℝ)/2) :
    μ.real (X ∩ S)=d := by
  rw [conditional_real μ S X hX,hm] at hhalf
  have hn : 2*d ≠ 0 := by positivity
  field_simp at hhalf
  nlinarith
end ThirdsNormalizedRestriction
end JigBundleModule42

/- Inlined module ThirdsConditionalCycle; original SHA256 21fabd2629f532c8ddabec4b9960cb5cdf0b0a36f94ecf92b522435b842bb428 -/
section JigBundleModule43
open MeasureTheory
namespace ThirdsConditionalCycle
open FourColorKernels
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma scale_two (f g h k : Ω × Ω → ℝ) :
    cycle4 μ f g h k=16*cycle4 μ (fun p => f p/2) (fun p => g p/2) (fun p => h p/2) (fun p => k p/2) := by
  unfold cycle4
  simp_rw [← integral_const_mul]
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
  intro t
  dsimp only
  ring
lemma unit_zero_cond (S : Set Ω) (hS : MeasurableSet S)
    (hprob : IsProbabilityMeasure (ProbabilityTheory.cond μ S)) (f g h k : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (bf : ∀ p, 0≤f p ∧ f p≤1) (bg : ∀ p, 0≤g p ∧ g p≤1)
    (bh : ∀ p, 0≤h p ∧ h p≤1) (bk : ∀ p, 0≤k p ∧ k p≤1)
    (hz : cycle4 μ f g h k=0) : cycle4 (ProbabilityTheory.cond μ S) f g h k=0 := by
  letI := hprob
  have he := (ThirdsFourCycleZero.zero_iff μ f g h k hf hg hh hk bf bg bh bk).mp hz
  apply (ThirdsFourCycleZero.zero_iff (ProbabilityTheory.cond μ S) f g h k hf hg hh hk bf bg bh bk).mpr
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [he] with x hx
  intro _
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [hx] with y hy
  intro _
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [hy] with z hz
  intro _
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [hz] with t ht
  exact fun _ => ht
lemma zero_cond (S : Set Ω) (hS : MeasurableSet S)
    (hprob : IsProbabilityMeasure (ProbabilityTheory.cond μ S)) (f g h k : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (bf : ∀ p, 0≤f p ∧ f p≤2) (bg : ∀ p, 0≤g p ∧ g p≤2)
    (bh : ∀ p, 0≤h p ∧ h p≤2) (bk : ∀ p, 0≤k p ∧ k p≤2)
    (hz : cycle4 μ f g h k=0) : cycle4 (ProbabilityTheory.cond μ S) f g h k=0 := by
  letI := hprob
  have hz' : cycle4 μ (fun p => f p/2) (fun p => g p/2) (fun p => h p/2) (fun p => k p/2)=0 := by
    have hs := scale_two μ f g h k
    rw [hz] at hs
    linarith
  have he := unit_zero_cond μ S hS hprob (fun p => f p/2) (fun p => g p/2)
    (fun p => h p/2) (fun p => k p/2) (hf.div_const 2) (hg.div_const 2) (hh.div_const 2) (hk.div_const 2)
    (fun p => ⟨by linarith [(bf p).1],by linarith [(bf p).2]⟩)
    (fun p => ⟨by linarith [(bg p).1],by linarith [(bg p).2]⟩)
    (fun p => ⟨by linarith [(bh p).1],by linarith [(bh p).2]⟩)
    (fun p => ⟨by linarith [(bk p).1],by linarith [(bk p).2]⟩) hz'
  rw [scale_two (ProbabilityTheory.cond μ S) f g h k,he]
  ring
end ThirdsConditionalCycle
end JigBundleModule43

/- Inlined module ThirdsAEAnchors; original SHA256 2c79dff298304e8294ce432673bb6b3c9704626be255832a610712e9604c95f3 -/
section JigBundleModule44
open MeasureTheory
namespace ThirdsAEAnchors
open FourColorKernels ThirdsCanonicalAnchors
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma bridge_measurable (W : Fin 6 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (i j : Fin 6) (u : Ω) : Measurable (bridge W i j u) :=
  (path_measurable W hm i j false u).add (path_measurable W hm i j true u)
lemma bridge_bounds (W : Fin 6 → Ω × Ω → ℝ) (hb : ∀ i p, 0≤W i p ∧ W i p≤1)
    (i j : Fin 6) (u : Ω) (p : Ω × Ω) : 0≤bridge W i j u p ∧ bridge W i j u p≤2 := by
  have h0 := path_bounds W hb i j false u p
  have h1 := path_bounds W hb i j true u p
  change 0≤path W i j false u p+path W i j true u p ∧ path W i j false u p+path W i j true u p≤2
  constructor <;> linarith
lemma bridge_congr (W Z : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hZ : ∀ i, Measurable (Z i)) (i j : Fin 6)
    (he : ∀ c, W c =ᵐ[μ.prod μ] Z c) :
    ∀ᵐ u ∂μ, bridge W i j u =ᵐ[μ.prod μ] bridge Z i j u := by
  have hout c := Measure.ae_ae_of_ae_prod (he c)
  have hin c := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq (he c))
  filter_upwards [hout i,hout j,hin i,hin j] with u hoi hoj hii hij
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (bridge_measurable W hW i j u) (bridge_measurable Z hZ i j u))).mpr
  filter_upwards [hii,hij] with x hix hjx
  filter_upwards [hoi,hoj] with y hiy hjy
  change W i (x,u)=Z i (x,u) at hix
  change W j (x,u)=Z j (x,u) at hjx
  change W i (u,y)=Z i (u,y) at hiy
  change W j (u,y)=Z j (u,y) at hjy
  simp only [bridge,path,Bool.false_eq_true,↓reduceIte]
  rw [hix,hjx,hiy,hjy]
lemma canonical_anchor_zeros (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0≤W i p ∧ W i p≤1)
    (hs : ∀ i, ∀ᵐ p ∂μ.prod μ, W i p=W i (p.2,p.1))
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (S : Set Ω) (hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    ∀ᵐ u ∂μ, ∀ᵐ v ∂μ,
      cycle4 (ProbabilityTheory.cond μ S) (W 0) (W 1) (bridge W 4 5 v) (bridge W 2 3 u)=0 ∧
      cycle4 (ProbabilityTheory.cond μ S) (W 0) (bridge W 2 3 u) (W 1) (bridge W 4 5 v)=0 := by
  let Z := fun i => symclip (W i)
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_symclip (hm i)
  have bZ : ∀ i p, 0≤Z i p ∧ Z i p≤1 := fun i p => symclip_bounds (W i) p
  have eZ : ∀ i, Z i =ᵐ[μ.prod μ] W i := fun i => symclip_eq_ae μ (W i) (hb i) (hs i)
  have hzZ : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => Z (σ i))=0 := by
    intro σ
    rw [LowSupportCycle.cycleNested_congr_ae (fun i => Z (σ i)) (fun i => W (σ i))
      (fun i => hZ (σ i)) (fun i => hm (σ i)) (fun i => eZ (σ i)),hz σ]
  have hp := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) hpos
  letI := hp
  have hac : (ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S) ≪ μ.prod μ :=
    ProbabilityTheory.cond_absolutelyContinuous.prod ProbabilityTheory.cond_absolutelyContinuous
  have hc0 := (eZ 0).filter_mono hac.ae_le
  have hc1 := (eZ 1).filter_mono hac.ae_le
  have hbr := bridge_congr μ Z W hZ hm 2 3 eZ
  have hbq := bridge_congr μ Z W hZ hm 4 5 eZ
  filter_upwards [ThirdsCanonicalAnchors.adjacent_anchor_zero μ Z hZ bZ hzZ,
    ThirdsCanonicalAnchors.alternating_anchor_zero μ Z hZ bZ hzZ,hbr] with u hau hbu hru
  filter_upwards [hau,hbu,hbq] with v hav hbv hqv
  have hrcond := hru.filter_mono hac.ae_le
  have hqcond := hqv.filter_mono hac.ae_le
  have hzA := ThirdsConditionalCycle.zero_cond μ S hS hp (Z 0) (Z 1)
    (bridge Z 4 5 v) (bridge Z 2 3 u) (hZ 0) (hZ 1)
    (bridge_measurable Z hZ 4 5 v) (bridge_measurable Z hZ 2 3 u)
    (fun p => ⟨(bZ 0 p).1,by linarith [(bZ 0 p).2]⟩)
    (fun p => ⟨(bZ 1 p).1,by linarith [(bZ 1 p).2]⟩)
    (bridge_bounds Z bZ 4 5 v) (bridge_bounds Z bZ 2 3 u) hav
  have hzB := ThirdsConditionalCycle.zero_cond μ S hS hp (Z 0) (bridge Z 2 3 u)
    (Z 1) (bridge Z 4 5 v) (hZ 0) (bridge_measurable Z hZ 2 3 u)
    (hZ 1) (bridge_measurable Z hZ 4 5 v)
    (fun p => ⟨(bZ 0 p).1,by linarith [(bZ 0 p).2]⟩) (bridge_bounds Z bZ 2 3 u)
    (fun p => ⟨(bZ 1 p).1,by linarith [(bZ 1 p).2]⟩) (bridge_bounds Z bZ 4 5 v) hbv
  constructor
  · rw [← cycle4_congr (ProbabilityTheory.cond μ S) hc0 hc1 hqcond hrcond]
    exact hzA
  · rw [← cycle4_congr (ProbabilityTheory.cond μ S) hc0 hrcond hc1 hqcond]
    exact hzB
end ThirdsAEAnchors
end JigBundleModule44

/- Inlined module ThirdsCycle4ZeroAE; original SHA256 107673fddfc9a2fe94bb9ef7822e9586e42f530b8ac435a9a6e7ae69bebde94a -/
section JigBundleModule45
open MeasureTheory
namespace ThirdsCycle4ZeroAE
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma zero_iff (f g h k : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (bf : ∀ᵐ p ∂μ.prod μ, 0 ≤ f p ∧ f p ≤ 1)
    (bg : ∀ᵐ p ∂μ.prod μ, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ᵐ p ∂μ.prod μ, 0 ≤ h p ∧ h p ≤ 1)
    (bk : ∀ᵐ p ∂μ.prod μ, 0 ≤ k p ∧ k p ≤ 1) :
    cycle4 μ f g h k=0 ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, ∀ᵐ t ∂μ,
      f (x,y)*g (y,z)*h (z,t)*k (t,x)=0 := by
  have eqclip (F : Ω × Ω → ℝ) (bF : ∀ᵐ p ∂μ.prod μ, 0 ≤ F p ∧ F p ≤ 1) : clip F =ᵐ[μ.prod μ] F := by
    filter_upwards [bF] with p hp
    simp [clip,min_eq_right hp.2,max_eq_right hp.1]
  have ef := eqclip f bf
  have eg := eqclip g bg
  have eh := eqclip h bh
  have ek := eqclip k bk
  have ez := ThirdsFourCycleZero.zero_iff μ (clip f) (clip g) (clip h) (clip k)
    (measurable_const.max (measurable_const.min hf)) (measurable_const.max (measurable_const.min hg))
    (measurable_const.max (measurable_const.min hh)) (measurable_const.max (measurable_const.min hk))
    (clip_bounds f) (clip_bounds g) (clip_bounds h) (clip_bounds k)
  rw [cycle4_congr μ ef eg eh ek] at ez
  rw [ez]
  have eks := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae ek)
  apply Filter.eventually_congr
  filter_upwards [Measure.ae_ae_of_ae_prod ef,eks] with x fx kx
  apply Filter.eventually_congr
  filter_upwards [fx,Measure.ae_ae_of_ae_prod eg] with y fy gy
  apply Filter.eventually_congr
  filter_upwards [gy,Measure.ae_ae_of_ae_prod eh] with z gz hz
  apply Filter.eventually_congr
  filter_upwards [hz,kx] with t ht kt
  change clip k (t,x)=k (t,x) at kt
  rw [fy,gz,ht,kt]
end ThirdsCycle4ZeroAE
end JigBundleModule45

/- Inlined module D10TriangleZeroAE; original SHA256 7de7f24caeb3a4160bf99d98e796a70e129c4d3aa507e88469088332f685a196 -/
section JigBundleModule46
open MeasureTheory
namespace D10TriangleZeroAE
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma zero_iff (f g h : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (bf : ∀ᵐ p ∂μ.prod μ, 0≤f p ∧ f p≤1)
    (bg : ∀ᵐ p ∂μ.prod μ, 0≤g p ∧ g p≤1)
    (bh : ∀ᵐ p ∂μ.prod μ, 0≤h p ∧ h p≤1) :
    (∫ x, ∫ y, ∫ z, f (x,y)*g (y,z)*h (z,x) ∂μ ∂μ ∂μ)=0 ↔
      ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, f (x,y)*g (y,z)*h (z,x)=0 := by
  have eqclip (F : Ω × Ω → ℝ) (bF : ∀ᵐ p ∂μ.prod μ, 0≤F p ∧ F p≤1) : clip F =ᵐ[μ.prod μ] F := by
    filter_upwards [bF] with p hp
    simp [clip,min_eq_right hp.2,max_eq_right hp.1]
  have ef := eqclip f bf
  have eg := eqclip g bg
  have eh := eqclip h bh
  have heq : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      clip f (x,y)*clip g (y,z)*clip h (z,x)=f (x,y)*g (y,z)*h (z,x) := by
    have hs := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae eh)
    filter_upwards [Measure.ae_ae_of_ae_prod ef,hs] with x fx hx
    filter_upwards [fx,Measure.ae_ae_of_ae_prod eg] with y fy gy
    filter_upwards [gy,hx] with z gz hz
    change clip h (z,x)=h (z,x) at hz
    rw [fy,gz,hz]
  have hi : (∫ x, ∫ y, ∫ z, clip f (x,y)*clip g (y,z)*clip h (z,x) ∂μ ∂μ ∂μ)=
      ∫ x, ∫ y, ∫ z, f (x,y)*g (y,z)*h (z,x) ∂μ ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    exact integral_congr_ae hy
  have hp := D10TriangleZero.zero_iff μ (clip f) (clip g) (clip h)
    (measurable_const.max (measurable_const.min hf))
    (measurable_const.max (measurable_const.min hg))
    (measurable_const.max (measurable_const.min hh)) (clip_bounds f) (clip_bounds g) (clip_bounds h)
  rw [hi] at hp
  rw [hp]
  apply Filter.eventually_congr
  filter_upwards [heq] with x hx
  apply Filter.eventually_congr
  filter_upwards [hx] with y hy
  apply Filter.eventually_congr
  filter_upwards [hy] with z hz
  rw [hz]
end D10TriangleZeroAE
end JigBundleModule46

/- Inlined module D10TwinTriangle; original SHA256 8e6a02910d3b73cefab58d4583aa56512ff0a28d174e932122dd8397299330ff -/
section JigBundleModule47
open MeasureTheory
namespace D10TwinTriangle
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma zero_rectangle (A B C : Ω×Ω → ℝ) (hC : Measurable C)
    (sB : ∀ᵐ p ∂μ.prod μ, B p=B (p.2,p.1))
    (S I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) (pS : μ S≠0)
    (rA : ∀ᵐ z ∂μ.restrict S, (fun x => A (z,x)) =ᵐ[μ] oneSet I)
    (rB : ∀ᵐ z ∂μ.restrict S, (fun y => B (z,y)) =ᵐ[μ] oneSet J)
    (hz : ∀ᵐ z ∂μ, ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, A (z,x)*C (x,y)*B (y,z)=0) :
    ∀ᵐ p ∂μ.prod μ, p.1∈I → p.2∈J → C p=0 := by
  have hs := Measure.ae_ae_of_ae_prod sB
  have good := rA.and (rB.and ((ae_restrict_of_ae hz).and (ae_restrict_of_ae hs)))
  obtain ⟨z,_,hA,hB,hzero,hBs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pS good
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hA,hzero] with x hAx hzx
  filter_upwards [hB,hBs,hzx] with y hBy hBsy hzy
  intro hx hy
  have h1 : A (z,x)=1 := by simpa [oneSet,hx] using hAx
  have h2 : B (y,z)=1 := hBsy.symm.trans (by simpa [oneSet,hy] using hBy)
  simpa [h1,h2] using hzy
end D10TwinTriangle
end JigBundleModule47

/- Inlined module D10BlockPropagationCore; original SHA256 dd005fa50e6f746f371cbdb1ed6c8256e30f958359a94d16504af727d7e4ab5f -/
section JigBundleModule48
namespace D10BlockPropagationCore
abbrev Matrix := Fin 6 → Fin 6 → Fin 6 → ℝ
abbrev Mask := Fin 6 → Fin 6 → Fin 6 → Bool
def Supports (x : Matrix) (A : Mask) : Prop := ∀ i j c, A i j c=false → x c i j=0

def palette (i j c : Fin 6) : Prop :=
  ({i,j,c} : Finset (Fin 6)) ∈
    ({{0,1,5},{0,2,4},{0,3,4},{0,3,5},{1,2,3},{1,3,4},{1,4,5},{2,3,5},{2,4,5},{3,4,5}} : Finset (Finset (Fin 6)))
instance (i j c : Fin 6) : Decidable (palette i j c) := inferInstanceAs (Decidable (_ ∈ (_ : Finset (Finset (Fin 6)))))
def initial (r : Fin 6) : Mask := fun i j c =>
  if i=r then decide (c=j) else if j=r then decide (c=i) else
  if i=j then decide (c≠i) else decide (c≠i ∧ c≠j ∧ palette i j c)
def prune (A : Mask) (i j c : Fin 6) : Mask := fun u v a =>
  if a=c ∧ ((u=i ∧ v≠j) ∨ (v=i ∧ u≠j)) then false else A u v a

def Rainbow (x : Matrix) : Prop :=
  ∃ a b c d e f : Fin 6, ∃ σ : Equiv.Perm (Fin 6),
    x (σ 0) a b=1 ∧ x (σ 1) b c=1 ∧ x (σ 2) c d=1 ∧
    x (σ 3) d e=1 ∧ x (σ 4) e f=1 ∧ x (σ 5) f a=1

lemma full_of_supported (x : Matrix) (part : ∀ i j, ∑ c, x c i j=1)
    (A : Mask) (hs : Supports x A) (i j c : Fin 6)
    (only : ∀ a, a≠c → A i j a=false) : x c i j=1 := by
  have eq : (∑ a, x a i j)=x c i j := by
    apply Finset.sum_eq_single c
    · intro a _ ha; exact hs i j a (only a ha)
    · simp
  rw [← eq]; exact part i j

lemma zero_elsewhere (x : Matrix) (nn : ∀ c i j, 0≤x c i j)
    (rows : ∀ c i, ∑ j, x c i j=1)
    (c i j : Fin 6) (full : x c i j=1) (k : Fin 6) (hk : k≠j) : x c i k=0 := by
  have eq := Finset.sum_erase_add Finset.univ (fun k => x c i k) (Finset.mem_univ j)
  rw [rows c i,full] at eq
  have hz : ∑ k ∈ Finset.univ.erase j, x c i k=0 := by linarith
  have hmem : k∈Finset.univ.erase j := by simp [hk]
  have hle := Finset.single_le_sum (s := Finset.univ.erase j) (f := fun k => x c i k)
    (fun k _ => nn c i k) hmem
  rw [hz] at hle
  exact le_antisymm hle (nn c i k)

lemma prune_sound (x : Matrix) (nn : ∀ c i j, 0≤x c i j)
    (symm : ∀ c i j, x c i j=x c j i) (part : ∀ i j, ∑ c, x c i j=1)
    (rows : ∀ c i, ∑ j, x c i j=1)
    (A : Mask) (hs : Supports x A) (i j c : Fin 6)
    (only : ∀ a, a≠c → A i j a=false) : Supports x (prune A i j c) := by
  have full := full_of_supported x part A hs i j c only
  intro u v a ha
  unfold prune at ha
  split_ifs at ha with h
  · obtain ⟨hac,h⟩ := h
    subst a
    rcases h with ⟨hui,hv⟩ | ⟨hvi,hu⟩
    · rw [hui]
      exact zero_elsewhere x nn rows c i j full v hv
    · rw [hvi, symm]
      exact zero_elsewhere x nn rows c i j full u hu
  · exact hs u v a ha
end D10BlockPropagationCore
end JigBundleModule48

/- Inlined module D10BlockInitial; original SHA256 a63b1f8a1ca127bf6072dcb8a8bc0d763d17f372396b92f0fcf3c71f7e786c58 -/
section JigBundleModule49
namespace D10BlockInitial
open D10BlockPropagationCore
lemma support (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j)
    (symm : ∀ c i j, x c i j = x c j i)
    (rows : ∀ c i, ∑ j, x c i j = 1) (r : Fin 6)
    (root : ∀ c j, x c r j = if c=j then 1 else 0)
    (forbidden : ∀ i j c, i≠j → c≠i → c≠j → ¬palette i j c → x c i j=0) :
    Supports x (initial r) := by
  intro i j c ha
  by_cases hi : i=r
  · subst i
    rw [root]
    have hn : c≠j := by simpa [initial] using ha
    simp [hn]
  by_cases hj : j=r
  · subst j
    rw [symm,root]
    have hn : c≠i := by simpa [initial,hi] using ha
    simp [hn]
  have zi : x i i j=0 := by
    have hf : x i i r=1 := by rw [symm,root]; simp
    exact zero_elsewhere x nn rows i i r hf j hj
  have zj : x j i j=0 := by
    rw [symm]
    have hf : x j j r=1 := by rw [symm,root]; simp
    exact zero_elsewhere x nn rows j j r hf i hi
  by_cases hij : i=j
  · subst j
    have hc : c=i := by simpa [initial,hi] using ha
    subst c
    exact zi
  by_cases hci : c=i
  · subst c; exact zi
  by_cases hcj : c=j
  · subst c; exact zj
  apply forbidden i j c hij hci hcj
  simpa [initial,hi,hj,hij,hci,hcj] using ha
end D10BlockInitial
end JigBundleModule49

/- Inlined module D10BlockPropagation; original SHA256 3e2e343b3b6b4983354245dd9a500b638e581047e967102499a5397b1fb7fac5 -/
section JigBundleModule50
namespace D10BlockPropagation
open D10BlockPropagationCore
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def m0_0 : Mask := initial 0
def m0_1 : Mask := prune m0_0 1 2 3
def m0_2 : Mask := prune m0_1 1 4 5
def m0_3 : Mask := prune m0_2 2 1 3
def m0_4 : Mask := prune m0_3 2 5 4
def m0_5 : Mask := prune m0_4 4 1 5
def m0_6 : Mask := prune m0_5 2 4 0
def m0_7 : Mask := prune m0_6 4 2 0
def m0_8 : Mask := prune m0_7 3 4 1
def m0_9 : Mask := prune m0_8 2 3 5
def m0_10 : Mask := prune m0_9 3 2 5
def m0_11 : Mask := prune m0_10 4 3 1
def m0_12 : Mask := prune m0_11 5 2 4
def m0_13 : Mask := prune m0_12 1 5 0
def m0_14 : Mask := prune m0_13 5 1 0
def m0_15 : Mask := prune m0_14 3 5 2
def m0_16 : Mask := prune m0_15 1 3 4
def m0_17 : Mask := prune m0_16 3 1 4
def m0_18 : Mask := prune m0_17 5 3 2
def m0_19 : Mask := prune m0_18 4 5 3
def m0_20 : Mask := prune m0_19 5 4 3
theorem case_0 (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j) (symm : ∀ c i j, x c i j = x c j i) (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1) (h0 : Supports x m0_0) : Rainbow x := by
  have h1 : Supports x m0_1 := prune_sound x nn symm part rows m0_0 h0 1 2 3 (by decide)
  have h2 : Supports x m0_2 := prune_sound x nn symm part rows m0_1 h1 1 4 5 (by decide)
  have h3 : Supports x m0_3 := prune_sound x nn symm part rows m0_2 h2 2 1 3 (by decide)
  have h4 : Supports x m0_4 := prune_sound x nn symm part rows m0_3 h3 2 5 4 (by decide)
  have h5 : Supports x m0_5 := prune_sound x nn symm part rows m0_4 h4 4 1 5 (by decide)
  have h6 : Supports x m0_6 := prune_sound x nn symm part rows m0_5 h5 2 4 0 (by decide)
  have h7 : Supports x m0_7 := prune_sound x nn symm part rows m0_6 h6 4 2 0 (by decide)
  have h8 : Supports x m0_8 := prune_sound x nn symm part rows m0_7 h7 3 4 1 (by decide)
  have h9 : Supports x m0_9 := prune_sound x nn symm part rows m0_8 h8 2 3 5 (by decide)
  have h10 : Supports x m0_10 := prune_sound x nn symm part rows m0_9 h9 3 2 5 (by decide)
  have h11 : Supports x m0_11 := prune_sound x nn symm part rows m0_10 h10 4 3 1 (by decide)
  have h12 : Supports x m0_12 := prune_sound x nn symm part rows m0_11 h11 5 2 4 (by decide)
  have h13 : Supports x m0_13 := prune_sound x nn symm part rows m0_12 h12 1 5 0 (by decide)
  have h14 : Supports x m0_14 := prune_sound x nn symm part rows m0_13 h13 5 1 0 (by decide)
  have h15 : Supports x m0_15 := prune_sound x nn symm part rows m0_14 h14 3 5 2 (by decide)
  have h16 : Supports x m0_16 := prune_sound x nn symm part rows m0_15 h15 1 3 4 (by decide)
  have h17 : Supports x m0_17 := prune_sound x nn symm part rows m0_16 h16 3 1 4 (by decide)
  have h18 : Supports x m0_18 := prune_sound x nn symm part rows m0_17 h17 5 3 2 (by decide)
  have h19 : Supports x m0_19 := prune_sound x nn symm part rows m0_18 h18 4 5 3 (by decide)
  have h20 : Supports x m0_20 := prune_sound x nn symm part rows m0_19 h19 5 4 3 (by decide)
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective (![0,1,2,3,4,5] : Fin 6 → Fin 6) (by decide)
  refine ⟨0, 0, 1, 1, 2, 5, σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact full_of_supported x part m0_20 h20 0 0 0 (by decide)
  · exact full_of_supported x part m0_20 h20 0 1 1 (by decide)
  · exact full_of_supported x part m0_20 h20 1 1 2 (by decide)
  · exact full_of_supported x part m0_20 h20 1 2 3 (by decide)
  · exact full_of_supported x part m0_20 h20 2 5 4 (by decide)
  · exact full_of_supported x part m0_20 h20 5 0 5 (by decide)
def m1_0 : Mask := initial 1
def m1_1 : Mask := prune m1_0 0 2 4
def m1_2 : Mask := prune m1_1 0 3 5
def m1_3 : Mask := prune m1_2 2 0 4
def m1_4 : Mask := prune m1_3 2 5 3
def m1_5 : Mask := prune m1_4 3 0 5
def m1_6 : Mask := prune m1_5 2 3 1
def m1_7 : Mask := prune m1_6 3 2 1
def m1_8 : Mask := prune m1_7 3 4 0
def m1_9 : Mask := prune m1_8 4 3 0
def m1_10 : Mask := prune m1_9 2 4 5
def m1_11 : Mask := prune m1_10 4 2 5
def m1_12 : Mask := prune m1_11 5 2 3
def m1_13 : Mask := prune m1_12 0 5 1
def m1_14 : Mask := prune m1_13 5 0 1
def m1_15 : Mask := prune m1_14 4 5 2
def m1_16 : Mask := prune m1_15 0 4 3
def m1_17 : Mask := prune m1_16 4 0 3
def m1_18 : Mask := prune m1_17 5 4 2
def m1_19 : Mask := prune m1_18 3 5 4
def m1_20 : Mask := prune m1_19 5 3 4
theorem case_1 (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j) (symm : ∀ c i j, x c i j = x c j i) (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1) (h0 : Supports x m1_0) : Rainbow x := by
  have h1 : Supports x m1_1 := prune_sound x nn symm part rows m1_0 h0 0 2 4 (by decide)
  have h2 : Supports x m1_2 := prune_sound x nn symm part rows m1_1 h1 0 3 5 (by decide)
  have h3 : Supports x m1_3 := prune_sound x nn symm part rows m1_2 h2 2 0 4 (by decide)
  have h4 : Supports x m1_4 := prune_sound x nn symm part rows m1_3 h3 2 5 3 (by decide)
  have h5 : Supports x m1_5 := prune_sound x nn symm part rows m1_4 h4 3 0 5 (by decide)
  have h6 : Supports x m1_6 := prune_sound x nn symm part rows m1_5 h5 2 3 1 (by decide)
  have h7 : Supports x m1_7 := prune_sound x nn symm part rows m1_6 h6 3 2 1 (by decide)
  have h8 : Supports x m1_8 := prune_sound x nn symm part rows m1_7 h7 3 4 0 (by decide)
  have h9 : Supports x m1_9 := prune_sound x nn symm part rows m1_8 h8 4 3 0 (by decide)
  have h10 : Supports x m1_10 := prune_sound x nn symm part rows m1_9 h9 2 4 5 (by decide)
  have h11 : Supports x m1_11 := prune_sound x nn symm part rows m1_10 h10 4 2 5 (by decide)
  have h12 : Supports x m1_12 := prune_sound x nn symm part rows m1_11 h11 5 2 3 (by decide)
  have h13 : Supports x m1_13 := prune_sound x nn symm part rows m1_12 h12 0 5 1 (by decide)
  have h14 : Supports x m1_14 := prune_sound x nn symm part rows m1_13 h13 5 0 1 (by decide)
  have h15 : Supports x m1_15 := prune_sound x nn symm part rows m1_14 h14 4 5 2 (by decide)
  have h16 : Supports x m1_16 := prune_sound x nn symm part rows m1_15 h15 0 4 3 (by decide)
  have h17 : Supports x m1_17 := prune_sound x nn symm part rows m1_16 h16 4 0 3 (by decide)
  have h18 : Supports x m1_18 := prune_sound x nn symm part rows m1_17 h17 5 4 2 (by decide)
  have h19 : Supports x m1_19 := prune_sound x nn symm part rows m1_18 h18 3 5 4 (by decide)
  have h20 : Supports x m1_20 := prune_sound x nn symm part rows m1_19 h19 5 3 4 (by decide)
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective (![2,0,1,5,3,4] : Fin 6 → Fin 6) (by decide)
  refine ⟨0, 0, 1, 1, 5, 2, σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact full_of_supported x part m1_20 h20 0 0 2 (by decide)
  · exact full_of_supported x part m1_20 h20 0 1 0 (by decide)
  · exact full_of_supported x part m1_20 h20 1 1 1 (by decide)
  · exact full_of_supported x part m1_20 h20 1 5 5 (by decide)
  · exact full_of_supported x part m1_20 h20 5 2 3 (by decide)
  · exact full_of_supported x part m1_20 h20 2 0 4 (by decide)
def m2_0 : Mask := initial 2
def m2_1 : Mask := prune m2_0 0 1 5
def m2_2 : Mask := prune m2_1 0 3 4
def m2_3 : Mask := prune m2_2 1 0 5
def m2_4 : Mask := prune m2_3 1 4 3
def m2_5 : Mask := prune m2_4 3 0 4
def m2_6 : Mask := prune m2_5 1 3 2
def m2_7 : Mask := prune m2_6 3 1 2
def m2_8 : Mask := prune m2_7 3 5 0
def m2_9 : Mask := prune m2_8 4 1 3
def m2_10 : Mask := prune m2_9 0 4 2
def m2_11 : Mask := prune m2_10 4 0 2
def m2_12 : Mask := prune m2_11 4 5 1
def m2_13 : Mask := prune m2_12 3 4 5
def m2_14 : Mask := prune m2_13 4 3 5
def m2_15 : Mask := prune m2_14 5 3 0
def m2_16 : Mask := prune m2_15 1 5 4
def m2_17 : Mask := prune m2_16 5 1 4
def m2_18 : Mask := prune m2_17 5 4 1
def m2_19 : Mask := prune m2_18 0 5 3
def m2_20 : Mask := prune m2_19 5 0 3
theorem case_2 (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j) (symm : ∀ c i j, x c i j = x c j i) (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1) (h0 : Supports x m2_0) : Rainbow x := by
  have h1 : Supports x m2_1 := prune_sound x nn symm part rows m2_0 h0 0 1 5 (by decide)
  have h2 : Supports x m2_2 := prune_sound x nn symm part rows m2_1 h1 0 3 4 (by decide)
  have h3 : Supports x m2_3 := prune_sound x nn symm part rows m2_2 h2 1 0 5 (by decide)
  have h4 : Supports x m2_4 := prune_sound x nn symm part rows m2_3 h3 1 4 3 (by decide)
  have h5 : Supports x m2_5 := prune_sound x nn symm part rows m2_4 h4 3 0 4 (by decide)
  have h6 : Supports x m2_6 := prune_sound x nn symm part rows m2_5 h5 1 3 2 (by decide)
  have h7 : Supports x m2_7 := prune_sound x nn symm part rows m2_6 h6 3 1 2 (by decide)
  have h8 : Supports x m2_8 := prune_sound x nn symm part rows m2_7 h7 3 5 0 (by decide)
  have h9 : Supports x m2_9 := prune_sound x nn symm part rows m2_8 h8 4 1 3 (by decide)
  have h10 : Supports x m2_10 := prune_sound x nn symm part rows m2_9 h9 0 4 2 (by decide)
  have h11 : Supports x m2_11 := prune_sound x nn symm part rows m2_10 h10 4 0 2 (by decide)
  have h12 : Supports x m2_12 := prune_sound x nn symm part rows m2_11 h11 4 5 1 (by decide)
  have h13 : Supports x m2_13 := prune_sound x nn symm part rows m2_12 h12 3 4 5 (by decide)
  have h14 : Supports x m2_14 := prune_sound x nn symm part rows m2_13 h13 4 3 5 (by decide)
  have h15 : Supports x m2_15 := prune_sound x nn symm part rows m2_14 h14 5 3 0 (by decide)
  have h16 : Supports x m2_16 := prune_sound x nn symm part rows m2_15 h15 1 5 4 (by decide)
  have h17 : Supports x m2_17 := prune_sound x nn symm part rows m2_16 h16 5 1 4 (by decide)
  have h18 : Supports x m2_18 := prune_sound x nn symm part rows m2_17 h17 5 4 1 (by decide)
  have h19 : Supports x m2_19 := prune_sound x nn symm part rows m2_18 h18 0 5 3 (by decide)
  have h20 : Supports x m2_20 := prune_sound x nn symm part rows m2_19 h19 5 0 3 (by decide)
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective (![1,5,0,4,2,3] : Fin 6 → Fin 6) (by decide)
  refine ⟨0, 0, 1, 1, 5, 5, σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact full_of_supported x part m2_20 h20 0 0 1 (by decide)
  · exact full_of_supported x part m2_20 h20 0 1 5 (by decide)
  · exact full_of_supported x part m2_20 h20 1 1 0 (by decide)
  · exact full_of_supported x part m2_20 h20 1 5 4 (by decide)
  · exact full_of_supported x part m2_20 h20 5 5 2 (by decide)
  · exact full_of_supported x part m2_20 h20 5 0 3 (by decide)
def m3_0 : Mask := initial 3
def m3_1 : Mask := prune m3_0 0 1 5
def m3_2 : Mask := prune m3_1 0 2 4
def m3_3 : Mask := prune m3_2 1 0 5
def m3_4 : Mask := prune m3_3 1 2 3
theorem case_3 (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j) (symm : ∀ c i j, x c i j = x c j i) (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1) (h0 : Supports x m3_0) : Rainbow x := by
  have h1 : Supports x m3_1 := prune_sound x nn symm part rows m3_0 h0 0 1 5 (by decide)
  have h2 : Supports x m3_2 := prune_sound x nn symm part rows m3_1 h1 0 2 4 (by decide)
  have h3 : Supports x m3_3 := prune_sound x nn symm part rows m3_2 h2 1 0 5 (by decide)
  have h4 : Supports x m3_4 := prune_sound x nn symm part rows m3_3 h3 1 2 3 (by decide)
  have hz : ∀ c, x c 1 4 = 0 := fun c => h4 1 4 c (by fin_cases c <;> decide)
  have hp := part 1 4
  simp only [hz, Finset.sum_const_zero] at hp
  norm_num at hp
def m4_0 : Mask := initial 4
def m4_1 : Mask := prune m4_0 0 1 5
def m4_2 : Mask := prune m4_1 0 2 4
theorem case_4 (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j) (symm : ∀ c i j, x c i j = x c j i) (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1) (h0 : Supports x m4_0) : Rainbow x := by
  have h1 : Supports x m4_1 := prune_sound x nn symm part rows m4_0 h0 0 1 5 (by decide)
  have h2 : Supports x m4_2 := prune_sound x nn symm part rows m4_1 h1 0 2 4 (by decide)
  have hz : ∀ c, x c 0 3 = 0 := fun c => h2 0 3 c (by fin_cases c <;> decide)
  have hp := part 0 3
  simp only [hz, Finset.sum_const_zero] at hp
  norm_num at hp
def m5_0 : Mask := initial 5
def m5_1 : Mask := prune m5_0 0 1 5
def m5_2 : Mask := prune m5_1 0 2 4
theorem case_5 (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j) (symm : ∀ c i j, x c i j = x c j i) (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1) (h0 : Supports x m5_0) : Rainbow x := by
  have h1 : Supports x m5_1 := prune_sound x nn symm part rows m5_0 h0 0 1 5 (by decide)
  have h2 : Supports x m5_2 := prune_sound x nn symm part rows m5_1 h1 0 2 4 (by decide)
  have hz : ∀ c, x c 0 3 = 0 := fun c => h2 0 3 c (by fin_cases c <;> decide)
  have hp := part 0 3
  simp only [hz, Finset.sum_const_zero] at hp
  norm_num at hp
theorem rainbow (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j) (symm : ∀ c i j, x c i j = x c j i) (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1) (r : Fin 6) (hs : Supports x (initial r)) : Rainbow x := by
  fin_cases r
  · exact case_0 x nn symm part rows hs
  · exact case_1 x nn symm part rows hs
  · exact case_2 x nn symm part rows hs
  · exact case_3 x nn symm part rows hs
  · exact case_4 x nn symm part rows hs
  · exact case_5 x nn symm part rows hs
end D10BlockPropagation
end JigBundleModule50

/- Inlined module ThirdsOrderedAnchors; original SHA256 5ab6e8ee0fece80a70a239a224d397647f49a6c4fe857ebd32be6800d7659130 -/
section JigBundleModule51
open MeasureTheory
namespace ThirdsOrderedAnchors
open ThirdsCanonicalAnchors
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma path_congr (W Z : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hZ : ∀ i, Measurable (Z i)) (i j : Fin 6)
    (he : ∀ c, W c =ᵐ[μ.prod μ] Z c) :
    ∀ᵐ u ∂μ, path W i j false u =ᵐ[μ.prod μ] path Z i j false u := by
  have hout := Measure.ae_ae_of_ae_prod (he j)
  have hin := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq (he i))
  filter_upwards [hout,hin] with u ho hi
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (path_measurable W hW i j false u)
    (path_measurable Z hZ i j false u))).mpr
  filter_upwards [hi] with x hx
  filter_upwards [ho] with y hy
  change W i (x,u)=Z i (x,u) at hx
  change W j (u,y)=Z j (u,y) at hy
  change W i (x,u)*W j (u,y)=Z i (x,u)*Z j (u,y)
  rw [hx,hy]
lemma adjacent_zero_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hm : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, cycle4 μ (W 0) (W 1)
      (path W 2 3 false v) (path W 4 5 false u)=0 := by
  let Z := fun i => clip (W i)
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_const.max (measurable_const.min (hm i))
  have bZ : ∀ i p, 0 ≤ Z i p ∧ Z i p ≤ 1 := fun i => clip_bounds (W i)
  have eZ : ∀ i, Z i =ᵐ[μ.prod μ] W i := by
    intro i
    filter_upwards [hb i] with p hp
    simp [Z,clip,min_eq_right hp.2,max_eq_right hp.1]
  have hzZ : LowSupportCycle.cycleNested (μ := μ) Z=0 := by
    rw [LowSupportCycle.cycleNested_congr_ae Z W hZ hm eZ,hz]
  have hc := ThirdsAnchoredCycle.adjacent_zero μ Z hZ bZ hzZ
  filter_upwards [hc,path_congr μ Z W hZ hm 4 5 eZ] with u hu eu
  filter_upwards [hu,path_congr μ Z W hZ hm 2 3 eZ] with v hv ev
  rw [← cycle4_congr μ (eZ 0) (eZ 1) ev eu]
  exact hv
end ThirdsOrderedAnchors
end JigBundleModule51

/- Inlined module ThirdsCycle4Restrict; original SHA256 3941049b1a32e0658dabe6ee1f6e4049061f30541448de9425b83ba1faf8db39 -/
section JigBundleModule52
open MeasureTheory
namespace ThirdsCycle4Restrict
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma middle_zero (f g g' h k : Ω × Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g') (hh : Measurable h) (hk : Measurable k)
    (bf : ∀ᵐ p ∂μ.prod μ, 0 ≤ f p ∧ f p ≤ 1)
    (bg : ∀ᵐ p ∂μ.prod μ, 0 ≤ g p ∧ g p ≤ 1)
    (bh : ∀ᵐ p ∂μ.prod μ, 0 ≤ h p ∧ h p ≤ 1)
    (bk : ∀ᵐ p ∂μ.prod μ, 0 ≤ k p ∧ k p ≤ 1)
    (hle : ∀ᵐ p ∂μ.prod μ, 0 ≤ g' p ∧ g' p ≤ g p)
    (hz : cycle4 μ f g h k=0) : cycle4 μ f g' h k=0 := by
  have bg' : ∀ᵐ p ∂μ.prod μ, 0 ≤ g' p ∧ g' p ≤ 1 := by
    filter_upwards [hle,bg] with p hp hbg
    exact ⟨hp.1,hp.2.trans hbg.2⟩
  have hzero := (ThirdsCycle4ZeroAE.zero_iff μ f g h k hf hg hh hk bf bg bh bk).mp hz
  apply (ThirdsCycle4ZeroAE.zero_iff μ f g' h k hf hg' hh hk bf bg' bh bk).mpr
  have bks := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae bk)
  filter_upwards [hzero,Measure.ae_ae_of_ae_prod bf,bks] with x hz bf bk
  filter_upwards [hz,bf,Measure.ae_ae_of_ae_prod hle] with y hz bf hl
  filter_upwards [hz,hl,Measure.ae_ae_of_ae_prod bh] with z hz hl bh
  filter_upwards [hz,bh,bk] with t hz bh bk
  change 0 ≤ k (t,x) ∧ k (t,x) ≤ 1 at bk
  have hlo := mul_nonneg (mul_nonneg (mul_nonneg bf.1 hl.1) bh.1) bk.1
  have hhi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl.2 bf.1) bh.1) bk.1
  exact le_antisymm (hhi.trans_eq hz) hlo
end ThirdsCycle4Restrict
end JigBundleModule52

/- Inlined module ThirdsAnchorExtremality; original SHA256 4489a5e1d6d903e89430fede180b537941f9efa5836c268f5fbb33a992927a83 -/
section JigBundleModule53
open MeasureTheory
namespace ThirdsAnchorExtremality

lemma scalar_extremality (u v a b : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (ha : a^2 ≤ u*v) (hb : b^2 ≤ u*v) (he : a*b=1) :
    u=1 ∧ v=1 ∧ a=b ∧ (a=1 ∨ a= -1) := by
  have huv : u*v ≤ 1 := by nlinarith
  have ha1 : a^2 ≤ 1 := ha.trans huv
  have hb1 : b^2 ≤ 1 := hb.trans huv
  have hab : a=b := by nlinarith [sq_nonneg (a-b)]
  have haa : a^2=1 := by nlinarith [he]
  have huu : u=1 := by nlinarith
  have hvv : v=1 := by nlinarith
  refine ⟨huu,hvv,hab,?_⟩
  rcases le_total 0 a with h | h
  · left; nlinarith
  · right; nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma bounded_square_integrable (r : Ω → ℝ) (hr : Measurable r)
    (br : ∀ᵐ x ∂μ, -1 ≤ r x ∧ r x ≤ 1) : Integrable (fun x => r x^2) μ := by
  apply LowSupportAnalysis.unit_integrable_ae (hr.pow_const 2)
  filter_upwards [br] with x hx
  exact ⟨sq_nonneg _,by nlinarith⟩

lemma unit_second_moment_sign (r : Ω → ℝ) (hr : Measurable r)
    (br : ∀ᵐ x ∂μ, -1 ≤ r x ∧ r x ≤ 1)
    (hm : (∫ x, r x^2 ∂μ)=1) : ∀ᵐ x ∂μ, r x=1 ∨ r x= -1 := by
  have hi := bounded_square_integrable μ r hr br
  have hle : (fun x => r x^2)  ≤ᵐ[μ] (fun _ => (1:ℝ)) := by
    filter_upwards [br] with x hx
    nlinarith
  have he : (fun x => r x^2) =ᵐ[μ] (fun _ => (1:ℝ)) :=
    (integral_eq_iff_of_ae_le hi (integrable_const _) hle).mp (by simpa using hm)
  filter_upwards [he] with x hx
  change r x^2=1 at hx
  rcases le_total 0 (r x) with h | h
  · left; nlinarith
  · right; nlinarith

lemma inner_one_alignment (r s : Ω → ℝ) (hr : Measurable r) (hs : Measurable s)
    (br : ∀ᵐ x ∂μ, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ᵐ x ∂μ, -1 ≤ s x ∧ s x ≤ 1)
    (mr : (∫ x, r x^2 ∂μ)=1) (ms : (∫ x, s x^2 ∂μ)=1)
    (hinner : (∫ x, r x*s x ∂μ)=1) : r =ᵐ[μ] s := by
  have ir := bounded_square_integrable μ r hr br
  have is := bounded_square_integrable μ s hs bs
  have ip : Integrable (fun x => r x*s x) μ := by
    apply Integrable.of_bound (hr.mul hs).aestronglyMeasurable 1
    filter_upwards [br,bs] with x hx hy
    change |r x*s x| ≤ 1
    rw [abs_mul]
    exact mul_le_one₀ (abs_le.mpr hx) (abs_nonneg _) (abs_le.mpr hy)
  have hf : (fun x => (r x-s x)^2)=(fun x => r x^2+s x^2-2*(r x*s x)) := by
    funext x; ring
  have iz : Integrable (fun x => (r x-s x)^2) μ := by
    rw [hf]; exact (ir.add is).sub (ip.const_mul 2)
  have hz : (∫ x, (r x-s x)^2 ∂μ)=0 := by
    rw [hf,integral_sub (f := fun x => r x^2+s x^2) (g := fun x => 2*(r x*s x)) (ir.add is) (ip.const_mul 2),integral_add (f := fun x => r x^2) (g := fun x => s x^2) ir is,integral_const_mul,mr,ms,hinner]
    norm_num
  have he := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) iz).mp hz
  filter_upwards [he] with x hx
  change (r x-s x)^2=0 at hx
  nlinarith [sq_nonneg (r x-s x)]

lemma anchor_alignment (r s : Ω → ℝ) (hr : Measurable r) (hs : Measurable s)
    (br : ∀ᵐ x ∂μ, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ᵐ x ∂μ, -1 ≤ s x ∧ s x ≤ 1)
    (b : ℝ)
    (hcs : (∫ x, r x*s x ∂μ)^2  ≤  (∫ x, r x^2 ∂μ)*(∫ x, s x^2 ∂μ))
    (hcontract : b^2  ≤  (∫ x, r x^2 ∂μ)*(∫ x, s x^2 ∂μ))
    (hextreme : (∫ x, r x*s x ∂μ)*b=1) :
    (∀ᵐ x ∂μ, r x=1 ∨ r x= -1) ∧
    (∀ᵐ x ∂μ, s x=1 ∨ s x= -1) ∧
    ((r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun x => -s x))) := by
  have bounds (f : Ω → ℝ) (hf : Measurable f) (bf : ∀ᵐ x ∂μ, -1 ≤ f x ∧ f x ≤ 1) :
      0 ≤ (∫ x, f x^2 ∂μ) ∧ (∫ x, f x^2 ∂μ) ≤ 1 := by
    apply LowSupportAnalysis.integral_unit_bounds_ae (hf.pow_const 2)
    filter_upwards [bf] with x hx
    exact ⟨sq_nonneg _,by nlinarith⟩
  obtain ⟨mr,ms,_,hinner⟩ := scalar_extremality _ _ _ b (bounds r hr br) (bounds s hs bs) hcs hcontract hextreme
  refine ⟨unit_second_moment_sign μ r hr br mr,unit_second_moment_sign μ s hs bs ms,?_⟩
  rcases hinner with hp | hn
  · exact Or.inl (inner_one_alignment μ r s hr hs br bs mr ms hp)
  · right
    apply inner_one_alignment μ r (fun x => -s x) hr hs.neg br
    · filter_upwards [bs] with x hx; constructor <;> linarith
    · exact mr
    · simpa only [neg_sq] using ms
    · simp_rw [mul_neg,integral_neg]
      linarith
end ThirdsAnchorExtremality
end JigBundleModule53

/- Inlined module ThirdsIntegralCauchy; original SHA256 6982825a4e4d178d316d7033ae2a436c04e62f46a509ec218c293779aec38a8c -/
section JigBundleModule54
open MeasureTheory
namespace ThirdsIntegralCauchy
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

lemma integral_cauchy (r s : Ω → ℝ)
    (ir : Integrable (fun x => r x^2) μ)
    (isq : Integrable (fun x => s x^2) μ)
    (ip : Integrable (fun x => r x*s x) μ) :
    (∫ x, r x*s x ∂μ)^2 ≤ (∫ x, r x^2 ∂μ)*(∫ x, s x^2 ∂μ) := by
  have hpoly : ∀ t : ℝ, 0 ≤ (∫ x, r x^2 ∂μ)*(t*t)+
      (2*(∫ x, r x*s x ∂μ))*t+(∫ x, s x^2 ∂μ) := by
    intro t
    have hn : 0 ≤ ∫ x, (t*r x+s x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have he : (fun x => (t*r x+s x)^2)=
        (fun x => t^2*r x^2+(2*t)*(r x*s x)+s x^2) := by funext x; ring
    rw [he,integral_add (f := fun x => t^2*r x^2+(2*t)*(r x*s x))
      (g := fun x => s x^2) ((ir.const_mul _).add (ip.const_mul _)) isq,
      integral_add (f := fun x => t^2*r x^2) (g := fun x => (2*t)*(r x*s x))
        (ir.const_mul _) (ip.const_mul _),integral_const_mul,integral_const_mul] at hn
    nlinarith
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  nlinarith

variable [IsProbabilityMeasure μ]
lemma bounded_product_integrable (r s : Ω → ℝ) (hr : Measurable r) (hs : Measurable s)
    (br : ∀ᵐ x ∂μ, -1 ≤ r x ∧ r x ≤ 1)
    (bs : ∀ᵐ x ∂μ, -1 ≤ s x ∧ s x ≤ 1) :
    Integrable (fun x => r x*s x) μ := by
  apply Integrable.of_bound (hr.mul hs).aestronglyMeasurable 1
  filter_upwards [br,bs] with x hx hy
  change |r x*s x| ≤ 1
  rw [abs_mul]
  exact mul_le_one₀ (abs_le.mpr hx) (abs_nonneg _) (abs_le.mpr hy)

lemma anchor_alignment (r s : Ω → ℝ) (hr : Measurable r) (hs : Measurable s)
    (br : ∀ᵐ x ∂μ, -1 ≤ r x ∧ r x ≤ 1)
    (bs : ∀ᵐ x ∂μ, -1 ≤ s x ∧ s x ≤ 1) (b : ℝ)
    (hcontract : b^2 ≤ (∫ x, r x^2 ∂μ)*(∫ x, s x^2 ∂μ))
    (hextreme : (∫ x, r x*s x ∂μ)*b=1) :
    (∀ᵐ x ∂μ, r x=1 ∨ r x= -1) ∧
    (∀ᵐ x ∂μ, s x=1 ∨ s x= -1) ∧
    ((r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun x => -s x))) := by
  apply ThirdsAnchorExtremality.anchor_alignment μ r s hr hs br bs b
  · exact integral_cauchy μ r s
      (ThirdsAnchorExtremality.bounded_square_integrable μ r hr br)
      (ThirdsAnchorExtremality.bounded_square_integrable μ s hs bs)
      (bounded_product_integrable μ r s hr hs br bs)
  · exact hcontract
  · exact hextreme
end ThirdsIntegralCauchy
end JigBundleModule54

/- Inlined module ThirdsWeightedVariance; original SHA256 7e988992c77f29e36c1db6ec94140c5036a46906d8700b86aaf0810fb6d0f930 -/
section JigBundleModule55
open MeasureTheory
namespace ThirdsWeightedVariance
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

lemma weighted_cauchy (w r : Ω → ℝ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (iw : Integrable w μ)
    (iwr : Integrable (fun x => w x*r x) μ)
    (iwr2 : Integrable (fun x => w x*r x^2) μ) :
    (∫ x, w x*r x ∂μ)^2 ≤ (∫ x, w x ∂μ)*(∫ x, w x*r x^2 ∂μ) := by
  have hp : ∀ t : ℝ, 0 ≤ (∫ x, w x ∂μ)*(t*t)+
      (2*(∫ x, w x*r x ∂μ))*t+(∫ x, w x*r x^2 ∂μ) := by
    intro t
    have hn : 0 ≤ ∫ x, w x*(t+r x)^2 ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hw] with x hx
      exact mul_nonneg hx (sq_nonneg _)
    have he : (fun x => w x*(t+r x)^2) =
        (fun x => t^2*w x+(2*t)*(w x*r x)+w x*r x^2) := by funext x; ring
    rw [he, integral_add (f := fun x => t^2*w x+(2*t)*(w x*r x))
      (g := fun x => w x*r x^2) ((iw.const_mul _).add (iwr.const_mul _)) iwr2,
      integral_add (f := fun x => t^2*w x) (g := fun x => (2*t)*(w x*r x))
      (iw.const_mul _) (iwr.const_mul _), integral_const_mul, integral_const_mul] at hn
    nlinarith
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith

variable [IsProbabilityMeasure μ]
lemma half_row_jensen (w r : Ω → ℝ) (hw : Measurable w) (hr : Measurable r)
    (bw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1)
    (hrow : ∫ x, w x ∂μ=(1:ℝ)/2) :
    (2*(∫ x, w x*r x ∂μ))^2 ≤ 2*(∫ x, w x*r x^2 ∂μ) := by
  have ir : Integrable (fun x => w x*r x) μ := by
    apply Integrable.of_bound (hw.mul hr).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    change |w x*r x| ≤ 1
    rw [abs_mul,abs_of_nonneg (bw x).1]
    exact mul_le_one₀ (bw x).2 (abs_nonneg _) (abs_le.mpr (br x))
  have b2 (x : Ω) : 0 ≤ r x^2 ∧ r x^2 ≤ 1 := by
    constructor
    · exact sq_nonneg _
    · nlinarith [sq_nonneg (r x-1),sq_nonneg (r x+1),(br x).1,(br x).2]
  have ir2 := FourColorKernels.unit_integrable μ (fun x => w x*r x^2)
    (hw.mul (hr.pow_const 2)) (fun x => FourColorKernels.mul_unit (bw x) (b2 x))
  have hh := weighted_cauchy μ w r (Filter.Eventually.of_forall (fun x => (bw x).1))
    (FourColorKernels.unit_integrable μ w hw bw) ir ir2
  rw [hrow] at hh
  nlinarith
lemma half_kernel_contraction (C : Ω × Ω → ℝ) (r : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2) :
    (∫ x, (2*TwoPairHalfSetOperator.act μ C r x)^2 ∂μ) ≤ ∫ x, r x^2 ∂μ := by
  let r2 : Ω → ℝ := fun x => r x^2
  have hr2 : Measurable r2 := hr.pow_const 2
  have br2 (x : Ω) : 0 ≤ r2 x ∧ r2 x ≤ 1 := by
    dsimp [r2]
    constructor
    · exact sq_nonneg _
    · nlinarith [(br x).1,(br x).2]
  have hj : ∀ᵐ x ∂μ, (2*TwoPairHalfSetOperator.act μ C r x)^2 ≤
      2*TwoPairHalfSetOperator.act μ C r2 x := by
    filter_upwards [hrow] with x hx
    exact half_row_jensen μ (fun y => C (x,y)) r (by fun_prop) hr
      (fun y => bC (x,y)) br hx
  have hi2 : Integrable (TwoPairHalfSetOperator.act μ C r2) μ :=
    FourColorKernels.unit_integrable μ _
      (TwoPairHalfSetOperator.measurable_act μ C r2 hC hr2)
      (TwoPairHalfSetOperator.act_bounds μ C r2 hC hr2 bC br2)
  have hi : Integrable (fun x => (2*TwoPairHalfSetOperator.act μ C r x)^2) μ := by
    apply Integrable.of_bound (((TwoPairHalfSetOperator.measurable_act μ C r hC hr).const_mul 2).pow_const 2).aestronglyMeasurable 1
    filter_upwards [hj,hrow] with x hx hd
    have hle := TwoPairHalfSetOperator.act_le_row μ C r2 hC hr2 bC br2 x
    rw [hd] at hle
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    linarith
  have hm := integral_mono_ae hi (hi2.const_mul 2) hj
  rw [integral_const_mul,
    TwoPairHalfSetOperator.act_total μ C r2 hC hr2 bC br2 sC ((1:ℝ)/2) hrow] at hm
  dsimp [r2] at hm
  linarith

end ThirdsWeightedVariance
end JigBundleModule55

/- Inlined module ThirdsSignedKernel; original SHA256 f87d1ea73cd86a2a3304fbc8bacdfdb54742eb20de1e60fb68a58fd05c2d449e -/
section JigBundleModule56
open MeasureTheory
namespace ThirdsSignedKernel
open TwoPairHalfSetOperator ThirdsIntegralCauchy ThirdsAnchorExtremality
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma scaled_act_bounds (C : Ω × Ω → ℝ) (r : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1)
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2) :
    ∀ᵐ x ∂μ, -1 ≤ 2*act μ C r x ∧ 2*act μ C r x ≤ 1 := by
  filter_upwards [hrow] with x hx
  have b2 (y : Ω) : 0 ≤ r y^2 ∧ r y^2 ≤ 1 := ⟨sq_nonneg _,by nlinarith [(br y).1,(br y).2]⟩
  have hj := ThirdsWeightedVariance.half_row_jensen μ (fun y => C (x,y)) r
    (by fun_prop) hr (fun y => bC (x,y)) br hx
  have hl := act_le_row μ C (fun y => r y^2) hC (hr.pow_const 2) bC b2 x
  rw [hx] at hl
  change (2*act μ C r x)^2 ≤ 2*act μ C (fun y => r y^2) x at hj
  constructor <;> nlinarith [sq_nonneg (2*act μ C r x-1),sq_nonneg (2*act μ C r x+1)]

lemma scaled_pairing_bound (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2) :
    (∫ x, (2*act μ C r x)*(2*act μ C s x) ∂μ)^2 ≤
      (∫ x, r x^2 ∂μ)*(∫ x, s x^2 ∂μ) := by
  let R := fun x => 2*act μ C r x
  let S := fun x => 2*act μ C s x
  have hR : Measurable R := (measurable_act μ C r hC hr).const_mul 2
  have hS : Measurable S := (measurable_act μ C s hC hs).const_mul 2
  have bR := scaled_act_bounds μ C r hC hr bC br hrow
  have bS := scaled_act_bounds μ C s hC hs bC bs hrow
  have hc := integral_cauchy μ R S (bounded_square_integrable μ R hR bR)
    (bounded_square_integrable μ S hS bS) (bounded_product_integrable μ R S hR hS bR bS)
  have cr := ThirdsWeightedVariance.half_kernel_contraction μ C r hC hr bC br sC hrow
  have cs := ThirdsWeightedVariance.half_kernel_contraction μ C s hC hs bC bs sC hrow
  have hm := mul_le_mul cr cs (integral_nonneg (fun x => sq_nonneg _))
    (integral_nonneg (fun x => sq_nonneg _))
  exact hc.trans hm

lemma actual_anchor_alignment (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (hextreme : (∫ x, r x*s x ∂μ)*
      (∫ x, (2*act μ C r x)*(2*act μ C s x) ∂μ)=1) :
    (∀ᵐ x ∂μ, r x=1 ∨ r x= -1) ∧
    (∀ᵐ x ∂μ, s x=1 ∨ s x= -1) ∧
    ((r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun x => -s x))) := by
  exact ThirdsIntegralCauchy.anchor_alignment μ r s hr hs
    (Filter.Eventually.of_forall br) (Filter.Eventually.of_forall bs) _
    (scaled_pairing_bound μ C r s hC hr hs bC br bs sC hrow) hextreme
end ThirdsSignedKernel
end JigBundleModule56

/- Inlined module ThirdsRankOneComp; original SHA256 abab4bd5085df842cbdc6fc2b7a17becc4062e40f828070e188a615be1245191 -/
section JigBundleModule57
open MeasureTheory
namespace ThirdsRankOneComp
open FourColorKernels TwoPairHalfSetOperator ThirdsIntegralCauchy
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
noncomputable def anchor (r : Ω → ℝ) (p : Ω × Ω) : ℝ := (1-r p.1*r p.2)/2
lemma signed_integrable (r : Ω → ℝ) (hr : Measurable r)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) : Integrable r μ := by
  apply Integrable.of_bound hr.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using abs_le.mpr (br x))
lemma anchor_bounds (r : Ω → ℝ) (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (p : Ω × Ω) :
    0 ≤ anchor r p ∧ anchor r p ≤ 1 := by
  have h : |r p.1*r p.2| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (abs_le.mpr (br _)) (abs_nonneg _) (abs_le.mpr (br _))
  have hh := abs_le.mp h
  dsimp [anchor]
  constructor <;> linarith
lemma measurable_anchor (r : Ω → ℝ) (hr : Measurable r) : Measurable (anchor r) := by
  unfold anchor; fun_prop
lemma anchor_comp (r s : Ω → ℝ) (hr : Measurable r) (hs : Measurable s)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (mr : ∫ x, r x ∂μ=0) (ms : ∫ x, s x ∂μ=0) (p : Ω × Ω) :
    comp μ (anchor r) (anchor s) p =
      (1+(∫ x, r x*s x ∂μ)*r p.1*s p.2)/4 := by
  have ir := signed_integrable μ r hr br
  have isq := signed_integrable μ s hs bs
  have ip := bounded_product_integrable μ r s hr hs
    (Filter.Eventually.of_forall br) (Filter.Eventually.of_forall bs)
  have he : (fun z => anchor r (p.1,z)*anchor s (z,p.2)) =
      (fun z => ((1:ℝ)-r p.1*r z-s p.2*s z+(r p.1*s p.2)*(r z*s z))/4) := by
    funext z; dsimp [anchor]; ring
  unfold comp
  rw [he,integral_div,
    integral_add (f := fun z => (1:ℝ)-r p.1*r z-s p.2*s z)
      (g := fun z => (r p.1*s p.2)*(r z*s z))
      (((integrable_const _).sub (ir.const_mul _)).sub (isq.const_mul _)) (ip.const_mul _),
    integral_sub (f := fun z => (1:ℝ)-r p.1*r z) (g := fun z => s p.2*s z)
      ((integrable_const _).sub (ir.const_mul _)) (isq.const_mul _),
    integral_sub (f := fun _ : Ω => (1:ℝ)) (g := fun z => r p.1*r z)
      (integrable_const _) (ir.const_mul _)]
  simp only [integral_const_mul,mr,ms,mul_zero,sub_zero]
  simp
  <;> ring

lemma complement_comp (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2) :
    comp μ C (fun p => 1-C p) =ᵐ[μ.prod μ] (fun p => (1:ℝ)/2-comp μ C C p) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_comp μ C (fun p => 1-C p) hC (by fun_prop))
    (measurable_const.sub (measurable_comp μ C C hC hC)))).mpr
  filter_upwards [hrow] with x hx
  apply Filter.Eventually.of_forall
  intro y
  change (∫ z, C (x,z)*(1-C (z,y)) ∂μ)=(1:ℝ)/2-∫ z, C (x,z)*C (z,y) ∂μ
  have he : (fun z => C (x,z)*(1-C (z,y)))=(fun z => C (x,z)-C (x,z)*C (z,y)) := by
    funext z; ring
  rw [he,integral_sub (unit_integrable μ _ (by fun_prop) (fun z => bC (x,z)))
    (unit_integrable μ _ (by fun_prop) (fun z => mul_unit (bC _) (bC _))),hx]
end ThirdsRankOneComp
end JigBundleModule57

/- Inlined module TwoPairKernelMass; original SHA256 4bf124325d039b5755ffb6f933750dc5c6758e35089d77e8dc5332184ea1072b -/
section JigBundleModule58
open MeasureTheory
namespace TwoPairKernelMass
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma total_comp (F G : Ω × Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (bF : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (bG : ∀ p, 0 ≤ G p ∧ G p ≤ 1)
    (sF : ∀ x y, F (x,y)=F (y,x)) (d : ℝ)
    (rF : ∀ᵐ x ∂μ, ∫ y, F (x,y) ∂μ=d) :
    (∫ p, comp μ F G p ∂μ.prod μ)=d*(∫ p, G p ∂μ.prod μ) := by
  have hi := unit_integrable (μ.prod μ) (comp μ F G)
    (measurable_comp μ F G hF hG) (comp_bounds μ F G hF hG bF bG)
  have hig := unit_integrable (μ.prod μ) G hG bG
  rw [integral_prod_symm _ hi,integral_prod_symm _ hig,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  exact act_total μ F (fun x => G (x,y)) hF (by fun_prop) bF
    (fun x => bG (x,y)) sF d rF

end TwoPairKernelMass
end JigBundleModule58

/- Inlined module ThirdsWeightedComp; original SHA256 9de4e73db7f647b543653205dc3576ea09f88dea665218be59cc70389d0b26e5 -/
section JigBundleModule59
open MeasureTheory
namespace ThirdsWeightedComp
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma four_bound (a b c d : ℝ) (ha : |a|≤1) (hb : |b|≤1) (hc : |c|≤1) (hd : |d|≤1) :
    |a*b*c*d|≤1 := by
  simp only [abs_mul]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ ha (abs_nonneg _) hb) (abs_nonneg _) hc) (abs_nonneg _) hd
lemma weighted_square (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) :
    (∫ p, comp μ C C p*r p.1*s p.2 ∂μ.prod μ)=
      ∫ z, act μ C r z*act μ C s z ∂μ := by
  have hi : Integrable (fun q : (Ω × Ω) × Ω =>
      C (q.1.1,q.2)*C (q.2,q.1.2)*r q.1.1*s q.1.2) ((μ.prod μ).prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    apply Filter.Eventually.of_forall
    intro q
    simp only [Real.norm_eq_abs]
    apply four_bound
    · simpa [abs_of_nonneg (bC _).1] using (bC (q.1.1,q.2)).2
    · simpa [abs_of_nonneg (bC _).1] using (bC (q.2,q.1.2)).2
    · exact abs_le.mpr (br _)
    · exact abs_le.mpr (bs _)
  calc
    _ = ∫ p, ∫ z, C (p.1,z)*C (z,p.2)*r p.1*s p.2 ∂μ ∂μ.prod μ := by
      simp only [comp,integral_mul_const]
    _ = ∫ z, ∫ p, C (p.1,z)*C (z,p.2)*r p.1*s p.2 ∂μ.prod μ ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      have he : (fun p : Ω × Ω => C (p.1,z)*C (z,p.2)*r p.1*s p.2)=
          (fun p => (C (z,p.1)*r p.1)*(C (z,p.2)*s p.2)) := by
        funext p; rw [sC p.1 z]; ring
      dsimp only
      rw [he]
      exact integral_prod_mul (fun x => C (z,x)*r x) (fun y => C (z,y)*s y)
end ThirdsWeightedComp
end JigBundleModule59

/- Inlined module ThirdsFirstTrace; original SHA256 1d54c7b1092e6cdb49653ee6b57769adb00b869f702c15c4ef840f2ad9485f18 -/
section JigBundleModule60
open MeasureTheory
namespace ThirdsFirstTrace
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma product_integral (K R : Ω → ℝ) (t : ℝ)
    (iK : Integrable K μ) (iR : Integrable R μ) (iKR : Integrable (fun x => K x*R x) μ)
    (mK : ∫ x, K x ∂μ=(1:ℝ)/4) (mR : ∫ x, R x ∂μ=0) :
    (∫ x, ((1:ℝ)/2-K x)*((1+t*R x)/4) ∂μ)=
      (1:ℝ)/16-t*(∫ x, K x*R x ∂μ)/4 := by
  have he : (fun x => ((1:ℝ)/2-K x)*((1+t*R x)/4))=
      (fun x => (1:ℝ)/8-K x/4+(t/8)*R x-(t/4)*(K x*R x)) := by funext x; ring
  rw [he, integral_sub (f := fun x => (1:ℝ)/8-K x/4+(t/8)*R x) (g := fun x => (t/4)*(K x*R x)) (((integrable_const _).sub (iK.div_const _)).add (iR.const_mul _)) (iKR.const_mul _),
    integral_add (f := fun x => (1:ℝ)/8-K x/4) (g := fun x => (t/8)*R x) ((integrable_const _).sub (iK.div_const _)) (iR.const_mul _),
    integral_sub (f := fun _ : Ω => (1:ℝ)/8) (g := fun x => K x/4) (integrable_const _) (iK.div_const _),integral_div]
  simp only [integral_div,integral_const_mul,integral_mul_const,mK,mR,mul_zero,add_zero]
  simp
  <;> ring

lemma first_trace (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (mr : ∫ x, r x ∂μ=0) (ms : ∫ x, s x ∂μ=0) :
    16*cycle4 μ C (fun p => 1-C p) (anchor s) (anchor r) =
      1-(∫ x, r x*s x ∂μ)*(∫ x, (2*act μ C r x)*(2*act μ C s x) ∂μ) := by
  let K := comp μ C C
  let R := fun p : Ω × Ω => r p.1*s p.2
  have hK : Measurable K := measurable_comp μ C C hC hC
  have bK := comp_bounds μ C C hC hC bC bC
  have iK : Integrable K (μ.prod μ) := unit_integrable _ _ hK bK
  have iR : Integrable R (μ.prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    apply Filter.Eventually.of_forall
    intro p
    change |r p.1*s p.2|≤1
    rw [abs_mul]
    exact mul_le_one₀ (abs_le.mpr (br _)) (abs_nonneg _) (abs_le.mpr (bs _))
  have iKR : Integrable (fun p => K p*R p) (μ.prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    apply Filter.Eventually.of_forall
    intro p
    change |K p*(r p.1*s p.2)|≤1
    rw [abs_mul,abs_of_nonneg (bK p).1,abs_mul]
    exact mul_le_one₀ (bK p).2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_le_one₀ (abs_le.mpr (br _)) (abs_nonneg _) (abs_le.mpr (bs _)))
  have mC : ∫ p, C p ∂μ.prod μ=(1:ℝ)/2 := by
    rw [integral_prod _ (unit_integrable _ _ hC bC)]
    calc
      _ = ∫ _ : Ω, (1:ℝ)/2 ∂μ := integral_congr_ae hrow
      _ = _ := by simp
  have mK : ∫ p, K p ∂μ.prod μ=(1:ℝ)/4 := by
    rw [TwoPairKernelMass.total_comp μ C C hC hC bC bC sC ((1:ℝ)/2) hrow,mC]
    norm_num
  have mR : ∫ p, R p ∂μ.prod μ=0 := by
    dsimp [R]; rw [integral_prod_mul r s,mr,ms]; norm_num
  have hp := product_integral (μ.prod μ) K R (∫ x, r x*s x ∂μ) iK iR iKR mK mR
  have he := FourColorCycleMatrix.comp_pair_cycle (μ := μ) C (fun p => 1-C p)
    (anchor r) (anchor s) hC (by fun_prop) (measurable_anchor r hr) (measurable_anchor s hs)
    bC (fun p => ⟨by linarith [(bC p).2],by linarith [(bC p).1]⟩)
    (anchor_bounds r br) (anchor_bounds s bs)
    (fun x y => by dsimp [anchor]; ring) (fun x y => by dsimp [anchor]; ring)
  rw [← he]
  have hc := complement_comp μ C hC bC hrow
  have hrewrite : (∫ p, comp μ C (fun p => 1-C p) p * comp μ (anchor r) (anchor s) p ∂μ.prod μ)=
      ∫ p, ((1:ℝ)/2-K p)*((1+(∫ x, r x*s x ∂μ)*R p)/4) ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [hc] with p hp
    rw [hp,anchor_comp μ r s hr hs br bs mr ms]
    dsimp [K,R]; ring
  rw [hrewrite,hp]
  have hw := ThirdsWeightedComp.weighted_square μ C r s hC hr hs bC br bs sC
  have hw' : (∫ p, K p*R p ∂μ.prod μ)=∫ z, act μ C r z*act μ C s z ∂μ := by
    simpa only [K,R,mul_assoc] using hw
  rw [hw']
  have hf : (fun x => (2*act μ C r x)*(2*act μ C s x))=
      (fun x => 4*(act μ C r x*act μ C s x)) := by funext x; ring
  rw [hf,integral_const_mul]
  ring
end ThirdsFirstTrace
end JigBundleModule60

/- Inlined module ThirdsMixedComp; original SHA256 595af9bfea0b4b76f9a0a662e7a136cef66fc3b630541cd83923bbfa1af5664e -/
section JigBundleModule61
open MeasureTheory
namespace ThirdsMixedComp
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma act_signed_bound (C : Ω × Ω → ℝ) (r : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (x : Ω) :
    -1 ≤ act μ C r x ∧ act μ C r x ≤ 1 := by
  have iC := unit_integrable μ (fun y => C (x,y)) (by fun_prop) (fun y => bC (x,y))
  have ip := ThirdsIntegralCauchy.bounded_product_integrable μ (fun y => C (x,y)) r
    (by fun_prop) hr (Filter.Eventually.of_forall (fun y => ⟨by linarith [(bC (x,y)).1],(bC _).2⟩))
    (Filter.Eventually.of_forall br)
  have hupper := integral_mono ip iC (fun y => mul_le_of_le_one_right (bC (x,y)).1 (br y).2)
  have hlower := integral_mono iC.neg ip (fun y => by change -C (x,y) ≤ C (x,y)*r y; nlinarith [(bC (x,y)).1,(br y).1])
  have hmass := FourColorCycleMatrix.integral_unit_bounds (μ := μ) (fun y => C (x,y))
    (by fun_prop) (fun y => bC (x,y))
  simp only [Pi.neg_apply,integral_neg] at hlower
  change -1 ≤ (∫ y, C (x,y)*r y ∂μ) ∧ (∫ y, C (x,y)*r y ∂μ) ≤ 1
  constructor <;> linarith

lemma right_anchor (C : Ω × Ω → ℝ) (r : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1)
    (x y : Ω) (hrow : ∫ z, C (x,z) ∂μ=(1:ℝ)/2) :
    comp μ C (anchor r) (x,y)=(1:ℝ)/4-act μ C r x*r y/2 := by
  have ip := ThirdsIntegralCauchy.bounded_product_integrable μ (fun z => C (x,z)) r
    (by fun_prop) hr (Filter.Eventually.of_forall (fun z => ⟨by linarith [(bC (x,z)).1],(bC _).2⟩))
    (Filter.Eventually.of_forall br)
  have he : (fun z => C (x,z)*anchor r (z,y))=
      (fun z => C (x,z)/2-(C (x,z)*r z)*r y/2) := by funext z; dsimp [anchor]; ring
  unfold comp
  rw [he,integral_sub (f := fun z => C (x,z)/2) (g := fun z => (C (x,z)*r z)*r y/2) ((unit_integrable μ _ (by fun_prop) (fun z => bC (x,z))).div_const 2)
    ((ip.mul_const _).div_const 2),integral_div,integral_div,integral_mul_const,hrow]
  dsimp [act]
  ring
lemma left_anchor_complement (C : Ω × Ω → ℝ) (s : Ω → ℝ)
    (hC : Measurable C) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) (ms : ∫ z, s z ∂μ=0)
    (x y : Ω) (hrow : ∫ z, C (y,z) ∂μ=(1:ℝ)/2) :
    comp μ (anchor s) (fun p => 1-C p) (x,y)=
      (1:ℝ)/4+s x*act μ C s y/2 := by
  have iC := unit_integrable μ (fun z => C (y,z)) (by fun_prop) (fun z => bC (y,z))
  have isq := signed_integrable μ s hs bs
  have ip := ThirdsIntegralCauchy.bounded_product_integrable μ (fun z => C (y,z)) s
    (by fun_prop) hs (Filter.Eventually.of_forall (fun z => ⟨by linarith [(bC (y,z)).1],(bC _).2⟩))
    (Filter.Eventually.of_forall bs)
  have he : (fun z => anchor s (x,z)*(1-C (z,y)))=
      (fun z => ((1:ℝ)-C (y,z)-s x*s z+s x*(C (y,z)*s z))/2) := by
    funext z; dsimp [anchor]; rw [sC z y]; ring
  unfold comp
  rw [he,integral_div,integral_add (f := fun z => (1:ℝ)-C (y,z)-s x*s z) (g := fun z => s x*(C (y,z)*s z)) (((integrable_const _).sub iC).sub (isq.const_mul _)) (ip.const_mul _),
    integral_sub (f := fun z => (1:ℝ)-C (y,z)) (g := fun z => s x*s z) ((integrable_const _).sub iC) (isq.const_mul _),
    integral_sub (f := fun _ : Ω => (1:ℝ)) (g := fun z => C (y,z)) (integrable_const _) iC,integral_const_mul,integral_const_mul,hrow,ms]
  simp only [mul_zero,sub_zero]
  simp [act]
  <;> ring
lemma signed_pairing (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x)) :
    (∫ x, r x*act μ C s x ∂μ)=(∫ x, act μ C r x*s x ∂μ) := by
  have hi : Integrable (fun p : Ω × Ω => r p.1*(C p*s p.2)) (μ.prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    apply Filter.Eventually.of_forall
    intro p
    change |r p.1*(C p*s p.2)|≤1
    rw [abs_mul,abs_mul,abs_of_nonneg (bC p).1]
    exact mul_le_one₀ (abs_le.mpr (br _)) (mul_nonneg (bC p).1 (abs_nonneg _))
      (mul_le_one₀ (bC p).2 (abs_nonneg _) (abs_le.mpr (bs _)))
  calc
    _ = ∫ x, ∫ y, r x*(C (x,y)*s y) ∂μ ∂μ := by simp only [act,integral_const_mul]
    _ = ∫ y, ∫ x, r x*(C (x,y)*s y) ∂μ ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∫ x, r x*(C (x,y)*s y) ∂μ)=(∫ x, C (y,x)*r x ∂μ)*s y
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [sC x y]; ring)
end ThirdsMixedComp
end JigBundleModule61

/- Inlined module ThirdsSecondTrace; original SHA256 be04c5fbdf60ba54b9b33d0a5110fc2c7df98c16e89fd6047df319093559e3b1 -/
section JigBundleModule62
open MeasureTheory
namespace ThirdsSecondTrace
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp ThirdsMixedComp
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma signed_mul_bounds (a b : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) :
    -1 ≤ a*b ∧ a*b ≤ 1 := by
  apply abs_le.mp
  rw [abs_mul]
  exact mul_le_one₀ (abs_le.mpr ha) (abs_nonneg _) (abs_le.mpr hb)
lemma separated_integral (a b r s : Ω → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hr : Measurable r) (hs : Measurable s)
    (ba : ∀ x, -1 ≤ a x ∧ a x ≤ 1) (bb : ∀ x, -1 ≤ b x ∧ b x ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (mr : ∫ x, r x ∂μ=0) (ms : ∫ x, s x ∂μ=0) :
    (∫ p : Ω × Ω, ((1:ℝ)/4-a p.1*r p.2/2)*((1:ℝ)/4+s p.1*b p.2/2) ∂μ.prod μ)=
      (1:ℝ)/16-(∫ x, a x*s x ∂μ)*(∫ x, r x*b x ∂μ)/4 := by
  let U := fun p : Ω × Ω => a p.1*r p.2
  let V := fun p : Ω × Ω => s p.1*b p.2
  have iU := signed_integrable (μ.prod μ) U (by fun_prop) (fun p => signed_mul_bounds _ _ (ba _) (br _))
  have iV := signed_integrable (μ.prod μ) V (by fun_prop) (fun p => signed_mul_bounds _ _ (bs _) (bb _))
  have iUV := signed_integrable (μ.prod μ) (fun p => U p*V p) (by fun_prop)
    (fun p => signed_mul_bounds _ _ (signed_mul_bounds _ _ (ba _) (br _)) (signed_mul_bounds _ _ (bs _) (bb _)))
  have mU : ∫ p, U p ∂μ.prod μ=0 := by dsimp [U]; rw [integral_prod_mul a r,mr]; ring
  have mV : ∫ p, V p ∂μ.prod μ=0 := by dsimp [V]; rw [integral_prod_mul s b,ms]; ring
  have mUV : (∫ p, U p*V p ∂μ.prod μ)=(∫ x, a x*s x ∂μ)*(∫ x, r x*b x ∂μ) := by
    have he : (fun p => U p*V p)=(fun p : Ω × Ω => (a p.1*s p.1)*(r p.2*b p.2)) := by
      funext p; dsimp [U,V]; ring
    rw [he]
    exact integral_prod_mul (fun x => a x*s x) (fun x => r x*b x)
  have he : (fun p : Ω × Ω => ((1:ℝ)/4-a p.1*r p.2/2)*((1:ℝ)/4+s p.1*b p.2/2))=
      (fun p => (1:ℝ)/16+V p/8-U p/8-(U p*V p)/4) := by funext p; dsimp [U,V]; ring
  rw [he,integral_sub (f := fun p => (1:ℝ)/16+V p/8-U p/8) (g := fun p => U p*V p/4)
    (((integrable_const _).add (iV.div_const _)).sub (iU.div_const _)) (iUV.div_const _),
    integral_sub (f := fun p => (1:ℝ)/16+V p/8) (g := fun p => U p/8)
    ((integrable_const _).add (iV.div_const _)) (iU.div_const _),
    integral_add (f := fun _ : Ω × Ω => (1:ℝ)/16) (g := fun p => V p/8)
    (integrable_const _) (iV.div_const _)]
  simp only [integral_div,mU,mV,mUV]
  simp

lemma second_trace (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0  ≤  C p ∧ C p  ≤  1)
    (br : ∀ x, -1  ≤  r x ∧ r x  ≤  1) (bs : ∀ x, -1  ≤  s x ∧ s x  ≤  1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (mr : ∫ x, r x ∂μ=0) (ms : ∫ x, s x ∂μ=0) :
    16*cycle4 μ C (anchor r) (fun p => 1-C p) (anchor s) =
      1-(∫ x, r x*(2*act μ C s x) ∂μ)^2 := by
  have he := FourColorCycleMatrix.comp_pair_cycle (μ := μ) C (anchor r)
    (anchor s) (fun p => 1-C p) hC (measurable_anchor r hr) (measurable_anchor s hs) (by fun_prop)
    bC (anchor_bounds r br) (anchor_bounds s bs)
    (fun p => ⟨by linarith [(bC p).2],by linarith [(bC p).1]⟩)
    (fun x y => by dsimp [anchor]; ring) (fun x y => by rw [sC x y])
  rw [← he]
  have hpair : ∀ᵐ p ∂μ.prod μ,
      comp μ C (anchor r) p * comp μ (anchor s) (fun p => 1-C p) p =
      ((1:ℝ)/4-act μ C r p.1*r p.2/2)*((1:ℝ)/4+s p.1*act μ C s p.2/2) := by
    have hm1 := measurable_comp μ C (anchor r) hC (measurable_anchor r hr)
    have hm2 := measurable_comp μ (anchor s) (fun p => 1-C p) (measurable_anchor s hs) (by fun_prop)
    have hmr := measurable_act μ C r hC hr
    have hms := measurable_act μ C s hC hs
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
    filter_upwards [hrow] with x hx
    filter_upwards [hrow] with y hy
    rw [right_anchor μ C r hC hr bC br x y hx,
      left_anchor_complement μ C s hC hs bC bs sC ms x y hy]
  rw [integral_congr_ae hpair,
    separated_integral μ (act μ C r) (act μ C s) r s
      (measurable_act μ C r hC hr) (measurable_act μ C s hC hs) hr hs
      (act_signed_bound μ C r hC hr bC br) (act_signed_bound μ C s hC hs bC bs) br bs mr ms]
  rw [← signed_pairing μ C r s hC hr hs bC br bs sC]
  have hf : (fun x => r x*(2*act μ C s x))=(fun x => 2*(r x*act μ C s x)) := by funext x; ring
  rw [hf,integral_const_mul]
  ring
end ThirdsSecondTrace
end JigBundleModule62

/- Inlined module ThirdsAnchorRigidity; original SHA256 f2ef570ade356315cc1f98d1ea504e8b51d3f9fd46fdbb04d14fc76220fdcf17 -/
section JigBundleModule63
open MeasureTheory
namespace ThirdsAnchorRigidity
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma unit_pairing_alignment (r t : Ω → ℝ) (hr : Measurable r) (ht : Measurable t)
    (br : ∀ᵐ x ∂μ, -1 ≤ r x ∧ r x ≤ 1) (bt : ∀ᵐ x ∂μ, -1 ≤ t x ∧ t x ≤ 1)
    (hp : (∫ x, r x*t x ∂μ)^2=1) :
    (r =ᵐ[μ] t) ∨ (r =ᵐ[μ] (fun x => -t x)) := by
  have hc := ThirdsIntegralCauchy.integral_cauchy μ r t
    (ThirdsAnchorExtremality.bounded_square_integrable μ r hr br)
    (ThirdsAnchorExtremality.bounded_square_integrable μ t ht bt)
    (ThirdsIntegralCauchy.bounded_product_integrable μ r t hr ht br bt)
  exact (ThirdsIntegralCauchy.anchor_alignment μ r t hr ht br bt _ hc
    (by simpa only [pow_two] using hp)).2.2
lemma rigidity (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (mr : ∫ x, r x ∂μ=0) (ms : ∫ x, s x ∂μ=0)
    (hz₁ : cycle4 μ C (fun p => 1-C p) (anchor s) (anchor r)=0)
    (hz₂ : cycle4 μ C (anchor r) (fun p => 1-C p) (anchor s)=0) :
    (∀ᵐ x ∂μ, r x=1 ∨ r x= -1) ∧
    (∀ᵐ x ∂μ, s x=1 ∨ s x= -1) ∧
    ((r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun x => -s x))) ∧
    (((fun x => 2*act μ C r x) =ᵐ[μ] r) ∨
      ((fun x => 2*act μ C r x) =ᵐ[μ] (fun x => -r x))) := by
  have hf := ThirdsFirstTrace.first_trace μ C r s hC hr hs bC br bs sC hrow mr ms
  rw [hz₁] at hf
  have he : (∫ x, r x*s x ∂μ)*(∫ x, (2*act μ C r x)*(2*act μ C s x) ∂μ)=1 := by linarith
  obtain ⟨rb,sb,hrs⟩ := ThirdsSignedKernel.actual_anchor_alignment μ C r s hC hr hs bC br bs sC hrow he
  have hg := ThirdsSecondTrace.second_trace μ C r s hC hr hs bC br bs sC hrow mr ms
  rw [hz₂] at hg
  have hp : (∫ x, r x*(2*act μ C s x) ∂μ)^2=1 := by linarith
  have hrt := unit_pairing_alignment μ r (fun x => 2*act μ C s x) hr
    ((measurable_act μ C s hC hs).const_mul 2) (Filter.Eventually.of_forall br)
    (ThirdsSignedKernel.scaled_act_bounds μ C s hC hs bC bs hrow) hp
  refine ⟨rb,sb,hrs,?_⟩
  rcases hrs with heq | hneg
  · have ha (x : Ω) : act μ C r x=act μ C s x := by
      apply integral_congr_ae
      filter_upwards [heq] with y hy
      rw [hy]
    rcases hrt with ht | ht
    · left; filter_upwards [ht] with x hx; rw [ha]; exact hx.symm
    · right; filter_upwards [ht] with x hx; rw [ha]; linarith
  · have ha (x : Ω) : act μ C r x= -act μ C s x := by
      change (∫ y, C (x,y)*r y ∂μ)= -(∫ y, C (x,y)*s y ∂μ)
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hneg] with y hy
      change r y= -s y at hy
      rw [hy]; ring
    rcases hrt with ht | ht
    · right; filter_upwards [ht] with x hx; rw [ha]; linarith
    · left; filter_upwards [ht] with x hx; rw [ha]; linarith
end ThirdsAnchorRigidity
end JigBundleModule63

/- Inlined module FourColorEqualRows; original SHA256 da261896a72bb1dfefb949668d02ad4bf19e316f887b3e0fbd5bcd4d45641d21 -/
section JigBundleModule64
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
end JigBundleModule64

/- Inlined module ThirdsEigenKernel; original SHA256 202d2ae8e981da95b6ba27434851f060d16224dc8dc371b4a76ffb0fac654eb5 -/
section JigBundleModule65
open MeasureTheory
namespace ThirdsEigenKernel
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma row_saturation (c r : Ω → ℝ) (hc : Measurable c) (hr : Measurable r)
    (bc : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1)
    (mr : ∫ x, r x ∂μ=0) (mc : ∫ x, c x ∂μ=(1:ℝ)/2)
    (t : ℝ) (ht : t^2=1) (hm : 2*(∫ x, c x*r x ∂μ)=t) :
    c =ᵐ[μ] (fun x => (1+t*r x)/2) := by
  have bt : -1≤t ∧ t≤1 := by constructor <;> nlinarith [sq_nonneg (t-1),sq_nonneg (t+1)]
  have ir := signed_integrable μ r hr br
  have ic := unit_integrable μ c hc bc
  have ip := ThirdsIntegralCauchy.bounded_product_integrable μ c r hc hr
    (Filter.Eventually.of_forall (fun x => ⟨by linarith [(bc x).1],(bc x).2⟩)) (Filter.Eventually.of_forall br)
  have bg (x : Ω) : 0 ≤ (1+t*r x)/2 ∧ (1+t*r x)/2 ≤ 1 := by
    have hb := ThirdsSecondTrace.signed_mul_bounds t (r x) bt (br x)
    constructor <;> linarith
  have mg : (∫ x, (1+t*r x)/2 ∂μ)=(1:ℝ)/2 := by
    rw [integral_div,integral_add (integrable_const _) (ir.const_mul _),integral_const_mul,mr]
    simp
  have mpg : (∫ x, c x*((1+t*r x)/2) ∂μ)=(1:ℝ)/2 := by
    have he : (fun x => c x*((1+t*r x)/2))=(fun x => (c x+t*(c x*r x))/2) := by funext x; ring
    rw [he,integral_div,integral_add (f := c) (g := fun x => t*(c x*r x)) ic (ip.const_mul _),integral_const_mul,mc]
    nlinarith
  have hh := FourColorEqualRows.half_rows_equal_indicator μ c (fun x => (1+t*r x)/2)
    hc (by fun_prop) (Filter.Eventually.of_forall bc) (Filter.Eventually.of_forall bg) mc mg mpg
  filter_upwards [hh] with x hx
  exact hx.1
lemma eigen_kernel (C : Ω × Ω → ℝ) (r : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1) (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1)
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (mr : ∫ x, r x ∂μ=0) (rb : ∀ᵐ x ∂μ, r x=1 ∨ r x= -1)
    (e : ℝ) (he : e^2=1) (hev : ∀ᵐ x ∂μ, 2*act μ C r x=e*r x) :
    C =ᵐ[μ.prod μ] (fun p => (1+e*r p.1*r p.2)/2) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hC (by fun_prop))).mpr
  filter_upwards [hrow,rb,hev] with x hx hrx hex
  have ht : (e*r x)^2=1 := by rcases hrx with h | h <;> rw [h] <;> nlinarith
  have hh := row_saturation μ (fun y => C (x,y)) r (by fun_prop) hr
    (fun y => bC (x,y)) br mr hx (e*r x) ht hex
  filter_upwards [hh] with y hy
  simpa only [mul_assoc] using hy
end ThirdsEigenKernel
end JigBundleModule65

/- Inlined module ThirdsNormalizedAnchor; original SHA256 d370793506adfa1bc9b46087d307aa9cfe097618c2a3a89ff914f340ba0e6e4e -/
section JigBundleModule66
open MeasureTheory
namespace ThirdsNormalizedAnchor
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma binary_half_set (r : Ω → ℝ) (hr : Measurable r)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (mr : ∫ x, r x ∂μ=0)
    (rb : ∀ᵐ x ∂μ, r x=1 ∨ r x= -1) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ.real S=(1:ℝ)/2 ∧
      r =ᵐ[μ] (fun x => 2*oneSet S x-1) := by
  have ir := signed_integrable μ r hr br
  have hi : (∫ x, (1+r x)/2 ∂μ)=(1:ℝ)*(1/2) := by
    rw [integral_div,integral_add (integrable_const _) ir,mr]
    simp
  have hb : ∀ᵐ x ∂μ, (1+r x)/2=0 ∨ (1+r x)/2=1 := by
    filter_upwards [rb] with x hx
    rcases hx with h | h <;> simp [h]
  obtain ⟨S,hS,mS,he⟩ := ThirdsDeterministicTransport.endpoint_set μ (fun x => (1+r x)/2)
    (by fun_prop) 1 (by norm_num) hb ((1:ℝ)/2) hi
  refine ⟨S,hS,mS,?_⟩
  filter_upwards [he] with x hx
  change (1+r x)/2=1*oneSet S x at hx
  linarith
lemma normalized_anchor (C : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ p, 0 ≤ C p ∧ C p ≤ 1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (sC : ∀ x y, C (x,y)=C (y,x))
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (mr : ∫ x, r x ∂μ=0) (ms : ∫ x, s x ∂μ=0)
    (hz₁ : cycle4 μ C (fun p => 1-C p) (anchor s) (anchor r)=0)
    (hz₂ : cycle4 μ C (anchor r) (fun p => 1-C p) (anchor s)=0) :
    ∃ S : Set Ω, ∃ e : ℝ, MeasurableSet S ∧ μ.real S=(1:ℝ)/2 ∧
      (e=1 ∨ e= -1) ∧ (r =ᵐ[μ] (fun x => 2*oneSet S x-1)) ∧
      ((r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun x => -s x))) ∧
      (C =ᵐ[μ.prod μ] (fun p => (1+e*r p.1*r p.2)/2)) := by
  obtain ⟨rb,sb,hrs,heig⟩ := ThirdsAnchorRigidity.rigidity μ C r s hC hr hs bC br bs sC hrow mr ms hz₁ hz₂
  obtain ⟨S,hS,mS,hrep⟩ := binary_half_set μ r hr br mr rb
  rcases heig with hp | hn
  · refine ⟨S,1,hS,mS,Or.inl rfl,hrep,hrs,?_⟩
    apply ThirdsEigenKernel.eigen_kernel μ C r hC hr bC br hrow mr rb 1 (by norm_num)
    filter_upwards [hp] with x hx
    simpa using hx
  · refine ⟨S,-1,hS,mS,Or.inr rfl,hrep,hrs,?_⟩
    apply ThirdsEigenKernel.eigen_kernel μ C r hC hr bC br hrow mr rb (-1) (by norm_num)
    filter_upwards [hn] with x hx
    simpa using hx
end ThirdsNormalizedAnchor
end JigBundleModule66

/- Inlined module ThirdsPairMass; original SHA256 db9c0a74443de7bffc5579c980253cc359130434b4725e90fdff37e9ce5ac8bb -/
section JigBundleModule67
open MeasureTheory
namespace ThirdsPairMass
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma binary_degree (a b c d : ℝ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) (hc : c=0 ∨ c=1) (hd : d=0 ∨ d=1)
    (ht : a+b+c+d=0 ∨ a+b+c+d=2) : a*(b+c+d)=a := by
  rcases ha with h|h <;> rcases hb with h'|h' <;> rcases hc with h''|h'' <;> rcases hd with h'''|h''' <;>
    simp_all <;> norm_num at *
lemma indicator_pair_integral (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ x, oneSet A x*oneSet B x ∂μ)=μ.real (A∩B) := by
  have he : (fun x => oneSet A x*oneSet B x)=oneSet (A∩B) := by
    classical
    funext x
    by_cases ha : x∈A <;> by_cases hb : x∈B <;> simp [oneSet,ha,hb]
  rw [he]
  simp [oneSet,integral_indicator (hA.inter hB)]
lemma degree_mass (A B C D : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (he : ∀ᵐ x ∂μ, oneSet A x*(oneSet B x+oneSet C x+oneSet D x)=oneSet A x) :
    μ.real (A∩B)+μ.real (A∩C)+μ.real (A∩D)=μ.real A := by
  have ints (X Y : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y) :
      Integrable (fun x => oneSet X x*oneSet Y x) μ :=
    unit_integrable μ _ ((oneSet_measurable X hX).mul (oneSet_measurable Y hY))
      (fun x => mul_unit (oneSet_bounds X x) (oneSet_bounds Y x))
  have he' : (fun x => oneSet A x*oneSet B x+oneSet A x*oneSet C x+oneSet A x*oneSet D x)=ᵐ[μ] oneSet A := by
    filter_upwards [he] with x hx
    nlinarith
  have hi := integral_congr_ae he'
  rw [integral_add (f := fun x => oneSet A x*oneSet B x+oneSet A x*oneSet C x)
    (g := fun x => oneSet A x*oneSet D x) ((ints A B hA hB).add (ints A C hA hC)) (ints A D hA hD),
    integral_add (f := fun x => oneSet A x*oneSet B x) (g := fun x => oneSet A x*oneSet C x)
      (ints A B hA hB) (ints A C hA hC),
    indicator_pair_integral μ A B hA hB,indicator_pair_integral μ A C hA hC,indicator_pair_integral μ A D hA hD] at hi
  simpa [oneSet,integral_indicator hA] using hi
lemma complementary_positive (T : Fin 4 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (d : ℝ) (hd : 0<d) (hm : ∀ i, μ.real (T i)=2*d)
    (hc : ∀ᵐ x ∂μ, (∑ i, oneSet (T i) x)=0 ∨ (∑ i, oneSet (T i) x)=2) :
    (0<μ.real (T 0∩T 1) ∧ 0<μ.real (T 2∩T 3)) ∨
    (0<μ.real (T 0∩T 2) ∧ 0<μ.real (T 1∩T 3)) ∨
    (0<μ.real (T 0∩T 3) ∧ 0<μ.real (T 1∩T 2)) := by
  have hc' : ∀ᵐ x ∂μ, oneSet (T 0) x+oneSet (T 1) x+oneSet (T 2) x+oneSet (T 3) x=0 ∨
      oneSet (T 0) x+oneSet (T 1) x+oneSet (T 2) x+oneSet (T 3) x=2 := by
    simpa only [Fin.sum_univ_four] using hc
  have h0 := degree_mass μ (T 0) (T 1) (T 2) (T 3) (hT 0) (hT 1) (hT 2) (hT 3) (by
    filter_upwards [hc'] with x hx
    exact binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) hx)
  have h1 := degree_mass μ (T 1) (T 0) (T 2) (T 3) (hT 1) (hT 0) (hT 2) (hT 3) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _)
    rcases hx with hx|hx
    · left; linarith
    · right; linarith)
  have h2 := degree_mass μ (T 2) (T 0) (T 1) (T 3) (hT 2) (hT 0) (hT 1) (hT 3) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _)
    rcases hx with hx|hx
    · left; linarith
    · right; linarith)
  have h3 := degree_mass μ (T 3) (T 0) (T 1) (T 2) (hT 3) (hT 0) (hT 1) (hT 2) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _)
    rcases hx with hx|hx
    · left; linarith
    · right; linarith)
  rw [hm 0] at h0
  rw [hm 1,Set.inter_comm (T 1) (T 0)] at h1
  rw [hm 2,Set.inter_comm (T 2) (T 0),Set.inter_comm (T 2) (T 1)] at h2
  rw [hm 3,Set.inter_comm (T 3) (T 0),Set.inter_comm (T 3) (T 1),Set.inter_comm (T 3) (T 2)] at h3
  have he0 : μ.real (T 0∩T 1)=μ.real (T 2∩T 3) := by linarith
  have he1 : μ.real (T 0∩T 2)=μ.real (T 1∩T 3) := by linarith
  have he2 : μ.real (T 0∩T 3)=μ.real (T 1∩T 2) := by linarith
  by_cases p0 : 0<μ.real (T 0∩T 1)
  · exact Or.inl ⟨p0,he0 ▸ p0⟩
  by_cases p1 : 0<μ.real (T 0∩T 2)
  · exact Or.inr (Or.inl ⟨p1,he1 ▸ p1⟩)
  have p2 : 0<μ.real (T 0∩T 3) := by linarith
  exact Or.inr (Or.inr ⟨p2,he2 ▸ p2⟩)
end ThirdsPairMass
end JigBundleModule67

/- Inlined module ThirdsCaseAPairs; original SHA256 2b2390c2ce727f6d3b0716454873bda965737e2e63807a9cd8a97e6b9cc051e0 -/
section JigBundleModule68
open MeasureTheory
namespace ThirdsCaseAPairs
open FourColorKernels TwoPairHalfSetOperator ThirdsDeterministicTransport
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma full_internal_transport (C : Ω × Ω → ℝ) (S T : Set Ω)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hm : μ.real T=μ.real S)
    (d : ℝ) (hd : 0<d)
    (hf : act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet T x))
    (hi : ∀ᵐ x ∂μ, x∈S → act μ C (oneSet S) x=d) :
    oneSet T =ᵐ[μ] oneSet S := by
  have he : (fun x => oneSet S x*oneSet T x) =ᵐ[μ] oneSet S := by
    filter_upwards [hf,hi] with x hx hix
    by_cases hxs : x∈S
    · have hv := hix hxs
      have ht : oneSet T x=1 := by
        change act μ C (oneSet S) x=d*oneSet T x at hx
        nlinarith
      simp only [ht,mul_one]
    · simp [oneSet,hxs]
  have hmST : μ.real (S∩T)=μ.real S := by
    have hh := integral_congr_ae he
    rw [ThirdsPairMass.indicator_pair_integral μ S T hS hT] at hh
    simpa [oneSet,integral_indicator hS] using hh
  have hIT := ThirdsLiteralLayout.full_subset_indicator μ (S∩T) T (hS.inter hT)
    Set.inter_subset_right (hmST.trans hm.symm)
  have hIS := ThirdsLiteralLayout.full_subset_indicator μ (S∩T) S (hS.inter hT)
    Set.inter_subset_left hmST
  exact hIT.symm.trans hIS
lemma remaining_pair_positive (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (S : Set Ω) (d : ℝ) (hd : 0<d) (hm : ∀ i, μ.real (T i)=2*d)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (h1 : oneSet (T 1) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, (∑ i, oneSet (T i) x)=2) :
    (0<μ.real (T 2∩T 3) ∧ 0<μ.real (T 4∩T 5)) ∨
    (0<μ.real (T 2∩T 4) ∧ 0<μ.real (T 3∩T 5)) ∨
    (0<μ.real (T 2∩T 5) ∧ 0<μ.real (T 3∩T 4)) := by
  let U : Fin 4 → Set Ω := ![T 2,T 3,T 4,T 5]
  have hU : ∀ i, MeasurableSet (U i) := by intro i; fin_cases i <;> first |exact hT 2|exact hT 3|exact hT 4|exact hT 5
  have mU : ∀ i, μ.real (U i)=2*d := by intro i; fin_cases i <;> first |exact hm 2|exact hm 3|exact hm 4|exact hm 5
  have hcU : ∀ᵐ x ∂μ, (∑ i, oneSet (U i) x)=0 ∨ (∑ i, oneSet (U i) x)=2 := by
    filter_upwards [hc,h0,h1] with x hx hx0 hx1
    simp only [Fin.sum_univ_six] at hx
    change oneSet (T 0) x=oneSet S x at hx0
    change oneSet (T 1) x=oneSet S x at hx1
    simp only [Fin.sum_univ_four]
    change oneSet (T 2) x+oneSet (T 3) x+oneSet (T 4) x+oneSet (T 5) x=0 ∨
      oneSet (T 2) x+oneSet (T 3) x+oneSet (T 4) x+oneSet (T 5) x=2
    rcases oneSet_binary S x with hs|hs
    · right; linarith
    · left; linarith
  exact ThirdsPairMass.complementary_positive μ U hU d hd mU hcU
lemma case_a_transport_pairs (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0<d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d)
    (hi0 : ∀ᵐ x ∂μ, x∈S → act μ (W 0) (oneSet S) x=d)
    (hi1 : ∀ᵐ x ∂μ, x∈S → act μ (W 1) (oneSet S) x=d) :
    ∃ T : Fin 6 → Set Ω, (∀ i, MeasurableSet (T i)) ∧ (∀ i, μ.real (T i)=2*d) ∧
      (∀ i, act μ (W i) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T i) x)) ∧
      ((0<μ.real (T 2∩T 3) ∧ 0<μ.real (T 4∩T 5)) ∨
       (0<μ.real (T 2∩T 4) ∧ 0<μ.real (T 3∩T 5)) ∨
       (0<μ.real (T 2∩T 5) ∧ 0<μ.real (T 3∩T 4))) := by
  have hall := fun c => set_transport μ (W c) (hW c) (bW c) (sW c) d (ne_of_gt hd) (hr c) S hS (hend c)
  choose T hT mT hf hrev hconf using hall
  have hmT : ∀ c, μ.real (T c)=2*d := fun c => (mT c).trans hmS
  have h0 := full_internal_transport μ (W 0) S (T 0) hS (hT 0) (mT 0) d hd (hf 0) hi0
  have h1 := full_internal_transport μ (W 1) S (T 1) hS (hT 1) (mT 1) d hd (hf 1) hi1
  have hc := ThirdsInternalCount.internal_count μ W hW bW hpart S hS d (ne_of_gt hd) hmS T hf
  exact ⟨T,hT,hmT,hf,remaining_pair_positive μ T hT S d hd hmT h0 h1 hc⟩
end ThirdsCaseAPairs
end JigBundleModule68

/- Inlined module ThirdsAnchorSelection; original SHA256 79394f765740c48f319aa0afc310d716ce541c6a3c87a36a458e543fd8ba0cb1 -/
section JigBundleModule69
open MeasureTheory
namespace ThirdsAnchorSelection
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma positive_pair_select (I J : Set Ω) (hi : 0<μ.real I) (hj : 0<μ.real J)
    (P : Ω → Ω → Prop) (hp : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, P x y) :
    ∃ x y, x∈I ∧ y∈J ∧ P x y := by
  have hi' : μ I ≠ 0 := by
    intro hz
    have hh : μ.real I=0 := by simp [measureReal_def,hz]
    linarith
  have hj' : μ J ≠ 0 := by
    intro hz
    have hh : μ.real J=0 := by simp [measureReal_def,hz]
    linarith
  obtain ⟨x,hx,hpx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hi' (ae_restrict_of_ae hp)
  obtain ⟨y,hy,hpy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hj' (ae_restrict_of_ae hpx)
  exact ⟨x,y,hx,hy,hpy⟩
lemma complementary_select (T : Fin 6 → Set Ω)
    (hc : (0<μ.real (T 2∩T 3) ∧ 0<μ.real (T 4∩T 5)) ∨
      (0<μ.real (T 2∩T 4) ∧ 0<μ.real (T 3∩T 5)) ∨
      (0<μ.real (T 2∩T 5) ∧ 0<μ.real (T 3∩T 4)))
    (P : Equiv.Perm (Fin 6) → Ω → Ω → Prop)
    (hp : ∀ σ, ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, P σ x y) :
    ∃ σ : Equiv.Perm (Fin 6), ∃ x y, σ 0=0 ∧ σ 1=1 ∧
      x∈T (σ 2)∩T (σ 3) ∧ y∈T (σ 4)∩T (σ 5) ∧ P σ x y := by
  rcases hc with h|h|h
  · let σ : Equiv.Perm (Fin 6) := Equiv.refl _
    obtain ⟨x,y,hx,hy,hP⟩ := positive_pair_select μ (T 2∩T 3) (T 4∩T 5) h.1 h.2 (P σ) (hp σ)
    exact ⟨σ,x,y,rfl,rfl,hx,hy,hP⟩
  · let σ : Equiv.Perm (Fin 6) := Equiv.swap 3 4
    obtain ⟨x,y,hx,hy,hP⟩ := positive_pair_select μ (T 2∩T 4) (T 3∩T 5) h.1 h.2 (P σ) (hp σ)
    refine ⟨σ,x,y,by decide,by decide,?_,?_,hP⟩
    · simpa [σ,Equiv.swap_apply_def] using hx
    · simpa [σ,Equiv.swap_apply_def] using hy
  · let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective (![0,1,2,5,3,4] : Fin 6 → Fin 6) (by decide)
    obtain ⟨x,y,hx,hy,hP⟩ := positive_pair_select μ (T 2∩T 5) (T 3∩T 4) h.1 h.2 (P σ) (hp σ)
    exact ⟨σ,x,y,rfl,rfl,hx,hy,hP⟩
end ThirdsAnchorSelection
end JigBundleModule69

/- Inlined module ThirdsCaseAAnchors; original SHA256 4631549ba0602c9bc50e9c79a329560e28f021590b2a6b462d7092626da9eb02 -/
section JigBundleModule70
open MeasureTheory
namespace ThirdsCaseAAnchors
open FourColorKernels TwoPairHalfSetOperator ThirdsCanonicalAnchors
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
def Facts (W : Fin 6 → Ω × Ω → ℝ) (S : Set Ω) (T : Fin 6 → Set Ω) (d : ℝ)
    (R : Ω → Prop) (σ : Equiv.Perm (Fin 6)) (u v : Ω) : Prop :=
  R u ∧ R v ∧
  (∀ c, act μ (W c) (oneSet S) u=d*oneSet (T c) u) ∧
  (∀ c, act μ (W c) (oneSet S) v=d*oneSet (T c) v) ∧
  cycle4 (ProbabilityTheory.cond μ S) (W (σ 0)) (W (σ 1))
    (bridge (fun c => W (σ c)) 4 5 v) (bridge (fun c => W (σ c)) 2 3 u)=0 ∧
  cycle4 (ProbabilityTheory.cond μ S) (W (σ 0)) (bridge (fun c => W (σ c)) 2 3 u)
    (W (σ 1)) (bridge (fun c => W (σ c)) 4 5 v)=0
lemma outside_active (T : Fin 6 → Set Ω) (S : Set Ω)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (h1 : oneSet (T 1) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, (∑ i, oneSet (T i) x)=2) :
    ∀ᵐ x ∂μ, ∀ c : Fin 6, c≠0 → c≠1 → x∈T c → x∉S := by
  filter_upwards [h0,h1,hc] with x hx0 hx1 hcount
  intro c hc0 hc1 hct hxs
  have hs : oneSet S x=1 := by simp [oneSet,hxs]
  have ht : oneSet (T c) x=1 := by simp [oneSet,hct]
  change oneSet (T 0) x=oneSet S x at hx0
  change oneSet (T 1) x=oneSet S x at hx1
  simp only [Fin.sum_univ_six] at hcount
  have hn (i : Fin 6) : 0≤oneSet (T i) x := (oneSet_bounds _ _).1
  fin_cases c <;> simp_all <;> nlinarith [hn 2,hn 3,hn 4,hn 5]

lemma case_a_anchors (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0<d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d)
    (hi0 : ∀ᵐ x ∂μ, x∈S → act μ (W 0) (oneSet S) x=d)
    (hi1 : ∀ᵐ x ∂μ, x∈S → act μ (W 1) (oneSet S) x=d)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (R : Ω → Prop) (hR : ∀ᵐ x ∂μ, R x) :
    ∃ T : Fin 6 → Set Ω, (∀ i, MeasurableSet (T i)) ∧ (∀ i, μ.real (T i)=2*d) ∧
      (∀ i, act μ (W i) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T i) x)) ∧
      ∃ σ : Equiv.Perm (Fin 6), ∃ u v, σ 0=0 ∧ σ 1=1 ∧
        u∈T (σ 2)∩T (σ 3) ∧ v∈T (σ 4)∩T (σ 5) ∧ u∉S ∧ v∉S ∧ Facts μ W S T d R σ u v := by
  obtain ⟨T,hT,mT,hf,hp⟩ := ThirdsCaseAPairs.case_a_transport_pairs μ W hW bW sW hpart d hd hr S hS hmS hend hi0 hi1
  have hSpos : μ S ≠ 0 := by
    intro hzero
    have hh : μ.real S=0 := by simp [measureReal_def,hzero]
    linarith
  have hact : ∀ᵐ x ∂μ, ∀ c, act μ (W c) (oneSet S) x=d*oneSet (T c) x := ae_all_iff.mpr hf
  have he0 := ThirdsCaseAPairs.full_internal_transport μ (W 0) S (T 0) hS (hT 0)
    ((mT 0).trans hmS.symm) d hd (hf 0) hi0
  have he1 := ThirdsCaseAPairs.full_internal_transport μ (W 1) S (T 1) hS (hT 1)
    ((mT 1).trans hmS.symm) d hd (hf 1) hi1
  have hcount := ThirdsInternalCount.internal_count μ W hW bW hpart S hS d (ne_of_gt hd) hmS T hf
  have hout := outside_active μ T S he0 he1 hcount
  let Q := fun (σ : Equiv.Perm (Fin 6)) u v => Facts μ W S T d R σ u v ∧
    (∀ c : Fin 6, c≠0 → c≠1 → u∈T c → u∉S) ∧
    (∀ c : Fin 6, c≠0 → c≠1 → v∈T c → v∉S)
  have hgood : ∀ σ : Equiv.Perm (Fin 6), ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, Q σ u v := by
    intro σ
    have hcy : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
      intro τ
      exact hz (τ.trans σ)
    have hc := ThirdsAEAnchors.canonical_anchor_zeros μ (fun c => W (σ c))
      (fun c => hW (σ c)) (fun c => bW (σ c)) (fun c => sW (σ c)) hcy S hS hSpos
    filter_upwards [hc,hact,hR,hout] with u hcu hau hRu hou
    filter_upwards [hcu,hact,hR,hout] with v hcv hav hRv hov
    exact ⟨⟨hRu,hRv,hau,hav,hcv.1,hcv.2⟩,hou,hov⟩
  obtain ⟨σ,u,v,hσ0,hσ1,hu,hv,hfacts,hou,hov⟩ := ThirdsAnchorSelection.complementary_select μ T hp Q hgood
  have hne (i : Fin 6) (hi0 : i≠0) (hi1 : i≠1) : σ i≠0 ∧ σ i≠1 := by
    constructor
    · intro h; exact hi0 (σ.injective (h.trans hσ0.symm))
    · intro h; exact hi1 (σ.injective (h.trans hσ1.symm))
  have h2 := hne 2 (by decide) (by decide)
  have h4 := hne 4 (by decide) (by decide)
  exact ⟨T,hT,mT,hf,σ,u,v,hσ0,hσ1,hu,hv,hou (σ 2) h2.1 h2.2 hu.1,
    hov (σ 4) h4.1 h4.2 hv.1,hfacts⟩
end ThirdsCaseAAnchors
end JigBundleModule70

/- Inlined module ThirdsRowCentering; original SHA256 a28279958e628feee808b0cdeb9fd70c265d2375ddbd2047a698407c623dd354 -/
section JigBundleModule71
open MeasureTheory
namespace ThirdsRowCentering
open FourColorKernels ThirdsRankOneComp
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma complementary_center (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ᵐ x ∂μ, 0≤f x ∧ f x≤1) (bg : ∀ᵐ x ∂μ, 0≤g x ∧ g x≤1)
    (hcap : ∀ᵐ x ∂μ, f x+g x≤1)
    (mf : ∫ x, f x ∂μ=(1:ℝ)/2) (mg : ∫ x, g x ∂μ=(1:ℝ)/2) :
    ∃ r : Ω → ℝ, Measurable r ∧ (∀ x, -1≤r x ∧ r x≤1) ∧ (∫ x, r x ∂μ)=0 ∧
      (f =ᵐ[μ] (fun x => (1+r x)/2)) ∧ (g =ᵐ[μ] (fun x => (1-r x)/2)) := by
  have iF := LowSupportAnalysis.unit_integrable_ae hf bf
  have iG := LowSupportAnalysis.unit_integrable_ae hg bg
  have he : (fun x => f x+g x) =ᵐ[μ] (fun _ => (1:ℝ)) :=
    (integral_eq_iff_of_ae_le (iF.add iG) (integrable_const _) hcap).mp (by
      simp only [Pi.add_apply]
      rw [integral_add iF iG,mf,mg]; norm_num)
  let r := fun x => 2*clip f x-1
  have hc : Measurable (clip f) := measurable_const.max (measurable_const.min hf)
  have hr : Measurable r := (hc.const_mul 2).sub_const 1
  have br (x : Ω) : -1≤r x ∧ r x≤1 := by
    have h := clip_bounds f x
    dsimp [r]; constructor <;> linarith
  have hclip : clip f =ᵐ[μ] f := by
    filter_upwards [bf] with x hx
    simp [clip,min_eq_right hx.2,max_eq_right hx.1]
  have ir : Integrable (clip f) μ := unit_integrable μ _ hc (clip_bounds f)
  have mr : (∫ x, r x ∂μ)=0 := by
    change (∫ x, 2*clip f x-1 ∂μ)=0
    rw [integral_sub (ir.const_mul 2) (integrable_const _),integral_const_mul,
      integral_congr_ae hclip,mf]
    simp
  refine ⟨r,hr,br,mr,?_,?_⟩
  · filter_upwards [hclip] with x hx
    change f x=(1+(2*clip f x-1))/2
    rw [hx]; ring
  · filter_upwards [hclip,he] with x hx hy
    change f x+g x=1 at hy
    change g x=(1-(2*clip f x-1))/2
    rw [hx]; linarith

lemma bridge_centered (W : Fin 6 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (i j : Fin 6) (u : Ω) (r : Ω → ℝ) (hr : Measurable r)
    (hf : (fun x => W i (u,x)) =ᵐ[μ] (fun x => (1+r x)/2))
    (hg : (fun x => W j (u,x)) =ᵐ[μ] (fun x => (1-r x)/2))
    (si : ∀ᵐ x ∂μ, W i (x,u)=W i (u,x))
    (sj : ∀ᵐ x ∂μ, W j (x,u)=W j (u,x)) :
    ThirdsCanonicalAnchors.bridge W i j u =ᵐ[μ.prod μ] anchor r := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (ThirdsAEAnchors.bridge_measurable W hm i j u) (measurable_anchor r hr))).mpr
  filter_upwards [hf,hg,si,sj] with x hfx hgx hix hjx
  filter_upwards [hf,hg] with y hfy hgy
  change W i (u,x)=(1+r x)/2 at hfx
  change W j (u,x)=(1-r x)/2 at hgx
  change W i (u,y)=(1+r y)/2 at hfy
  change W j (u,y)=(1-r y)/2 at hgy
  change W i (x,u)*W j (u,y)+W j (x,u)*W i (u,y)=(1-r x*r y)/2
  rw [hix,hjx,hfx,hgx,hfy,hgy]
  ring
end ThirdsRowCentering
end JigBundleModule71

/- Inlined module ThirdsMixingAnchor; original SHA256 3f9e8faf3ba244aa33623259edeedea87e97862aa1b8ea1d8ab65e0e0b0165ef -/
section JigBundleModule72
open MeasureTheory
namespace ThirdsMixingAnchor
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma integral_mul_indicator (f : Ω → ℝ) (X : Set Ω) (hX : MeasurableSet X) :
    (∫ x, f x*oneSet X x ∂μ)=∫ x in X, f x ∂μ := by
  rw [← integral_indicator hX]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by by_cases hx : x∈X <;> simp [oneSet,hx])
lemma same_half_mass (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (X : Set Ω) (hX : MeasurableSet X) :
    (∫ x in X, ∫ y in X, f x*(1-f y)+(1-f x)*f y ∂μ ∂μ)=
      2*(∫ x in X, f x ∂μ)*(μ.real X-(∫ x in X, f x ∂μ)) := by
  have iF := (LowSupportAnalysis.unit_integrable_ae hf bf).restrict (s := X)
  have iG : Integrable (fun x => 1-f x) (μ.restrict X) := (integrable_const _).sub iF
  have mg : (∫ x in X, 1-f x ∂μ)=μ.real X-(∫ x in X, f x ∂μ) := by
    rw [integral_sub (integrable_const _) iF]
    simp
  have hin (x : Ω) : (∫ y in X, f x*(1-f y)+(1-f x)*f y ∂μ)=
      f x*(μ.real X-(∫ y in X, f y ∂μ))+(1-f x)*(∫ y in X, f y ∂μ) := by
    rw [integral_add (iG.const_mul _) (iF.const_mul _),integral_const_mul,integral_const_mul,mg]
  simp_rw [hin]
  rw [integral_add (iF.mul_const _) (iG.mul_const _),integral_mul_const,integral_mul_const,mg]
  ring
lemma endpoint_alignment (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (mf : ∫ x, f x ∂μ=(1:ℝ)/2)
    (X : Set Ω) (hX : MeasurableSet X) (mX : μ.real X=(1:ℝ)/2)
    (hend : (∫ x in X, f x ∂μ)=0 ∨ (∫ x in X, f x ∂μ)=(1:ℝ)/2) :
    (f =ᵐ[μ] oneSet X) ∨ (f =ᵐ[μ] (fun x => 1-oneSet X x)) := by
  have hI := oneSet_measurable X hX
  have bI : ∀ᵐ x ∂μ, 0 ≤ oneSet X x ∧ oneSet X x ≤ 1 := Filter.Eventually.of_forall (oneSet_bounds X)
  have mI : (∫ x, oneSet X x ∂μ)=(1:ℝ)/2 := by simpa [oneSet,integral_indicator hX] using mX
  rcases hend with hz|hh
  · right
    have bg : ∀ᵐ x ∂μ, 0 ≤ 1-oneSet X x ∧ 1-oneSet X x ≤ 1 := by
      filter_upwards [bI] with x hx; constructor <;> linarith
    have mg : (∫ x, 1-oneSet X x ∂μ)=(1:ℝ)/2 := by
      rw [integral_sub (integrable_const _) (LowSupportAnalysis.unit_integrable_ae hI bI),mI]; simp; norm_num
    have ip := LowSupportAnalysis.unit_integrable_ae (hf.mul hI)
      (bf.and bI |>.mono fun x h => LowSupportAnalysis.mul_unit h.1 h.2)
    have mp : (∫ x, f x*(1-oneSet X x) ∂μ)=(1:ℝ)/2 := by
      simp_rw [mul_sub,mul_one]
      rw [integral_sub (f := f) (g := fun x => f x*oneSet X x) (LowSupportAnalysis.unit_integrable_ae hf bf) ip,
        integral_mul_indicator μ f X hX,hz,mf]; ring
    exact (FourColorEqualRows.half_rows_equal_indicator μ f (fun x => 1-oneSet X x) hf
      (measurable_const.sub hI) bf bg mf mg mp).mono (fun _ h => h.1)
  · left
    have mp : (∫ x, f x*oneSet X x ∂μ)=(1:ℝ)/2 := by rw [integral_mul_indicator μ f X hX,hh]
    exact (FourColorEqualRows.half_rows_equal_indicator μ f (oneSet X) hf hI bf bI mf mI mp).mono (fun _ h => h.1)
lemma mixing_positive (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (mf : ∫ x, f x ∂μ=(1:ℝ)/2)
    (X : Set Ω) (hX : MeasurableSet X) (mX : μ.real X=(1:ℝ)/2)
    (hn : ¬ ((f =ᵐ[μ] oneSet X) ∨ (f =ᵐ[μ] (fun x => 1-oneSet X x)))) :
    0 < (∫ x in X, ∫ y in X, f x*(1-f y)+(1-f x)*f y ∂μ ∂μ) := by
  have iF := (LowSupportAnalysis.unit_integrable_ae hf bf).restrict (s := X)
  have bb : ∀ᵐ x ∂μ.restrict X, 0 ≤ f x ∧ f x ≤ 1 := ae_restrict_of_ae bf
  have hlo : 0 ≤ ∫ x in X, f x ∂μ := integral_nonneg_of_ae (bb.mono fun _ h => h.1)
  have hhi : (∫ x in X, f x ∂μ) ≤ (1:ℝ)/2 := by
    have hh := integral_mono_ae iF (integrable_const (1:ℝ)) (bb.mono fun _ h => h.2)
    simpa [mX] using hh
  have hn0 : (∫ x in X, f x ∂μ) ≠ 0 := fun h => hn (endpoint_alignment μ f hf bf mf X hX mX (Or.inl h))
  have hn1 : (∫ x in X, f x ∂μ) ≠ (1:ℝ)/2 := fun h => hn (endpoint_alignment μ f hf bf mf X hX mX (Or.inr h))
  rw [same_half_mass μ f hf bf X hX,mX]
  have hs : 0 < ∫ x in X, f x ∂μ := lt_of_le_of_ne hlo (Ne.symm hn0)
  have ht : 0 < (1:ℝ)/2-(∫ x in X, f x ∂μ) := sub_pos.mpr (lt_of_le_of_ne hhi hn1)
  exact mul_pos (mul_pos (by norm_num) hs) ht
end ThirdsMixingAnchor
end JigBundleModule72

/- Inlined module ThirdsFivePathFactor; original SHA256 028a20c6facf3c84dc405d2672631503918d7eb8bebc6808e2c1f520b65c52d6 -/
section JigBundleModule73
open MeasureTheory
namespace ThirdsFivePathFactor
open TwoPairHalfSetOperator
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
def tensor (f g : Ω → ℝ) (p : Ω × Ω) : ℝ := f p.1*g p.2
lemma factor (F : Ω × Ω → ℝ) (I D E A : Ω → ℝ) :
    cycle4 μ F (tensor I I) (tensor D E) (tensor I A)=
      (∫ z, I z*D z ∂μ)*(∫ t, E t*I t ∂μ)*(∫ x, A x*(∫ y, F (x,y)*I y ∂μ) ∂μ) := by
  have hp (x y z t : Ω) : F (x,y)*tensor I I (y,z)*tensor D E (z,t)*tensor I A (t,x)=
      (I z*D z)*((E t*I t)*(A x*(F (x,y)*I y))) := by unfold tensor; ring
  have hleaf (x y : Ω) :
      (∫ z, ∫ t, (I z*D z)*((E t*I t)*(A x*(F (x,y)*I y))) ∂μ ∂μ)=
      (∫ z, I z*D z ∂μ)*((∫ t, E t*I t ∂μ)*(A x*(F (x,y)*I y))) := by
    simp_rw [integral_const_mul,integral_mul_const]
  unfold cycle4
  simp_rw [hp,hleaf,integral_const_mul]
  ring
lemma positive_forces_zero (F : Ω × Ω → ℝ) (X : Set Ω) (hX : MeasurableSet X)
    (D E A : Ω → ℝ) (hF : Measurable F) (hA : Measurable A)
    (bF : ∀ᵐ p ∂μ.prod μ, 0 ≤ F p ∧ F p ≤ 1)
    (bA : ∀ᵐ x ∂μ, 0 ≤ A x ∧ A x ≤ 1)
    (hD : 0 < ∫ z in X, D z ∂μ) (hE : 0 < ∫ t in X, E t ∂μ)
    (hz : cycle4 μ F (tensor (oneSet X) (oneSet X)) (tensor D E) (tensor (oneSet X) A)=0) :
    ∀ᵐ x ∂μ, A x*(∫ y in X, F (x,y) ∂μ)=0 := by
  have hfactor := factor μ F (oneSet X) D E A
  have md : (∫ z, oneSet X z*D z ∂μ)=∫ z in X, D z ∂μ := by
    rw [← ThirdsMixingAnchor.integral_mul_indicator μ D X hX]
    congr 1; funext z; ring
  have me := ThirdsMixingAnchor.integral_mul_indicator μ E X hX
  have mi (x : Ω) := ThirdsMixingAnchor.integral_mul_indicator μ (fun y => F (x,y)) X hX
  rw [md,me] at hfactor
  simp_rw [mi] at hfactor
  have hz' : (∫ x, A x*(∫ y in X, F (x,y) ∂μ) ∂μ)=0 := by
    rw [hz] at hfactor
    exact (mul_eq_zero.mp hfactor.symm).resolve_left (ne_of_gt (mul_pos hD hE))
  have hm : Measurable (fun x => ∫ y in X, F (x,y) ∂μ) := by fun_prop
  have bb : ∀ᵐ x ∂μ, 0 ≤ (∫ y in X, F (x,y) ∂μ) ∧ (∫ y in X, F (x,y) ∂μ) ≤ 1 := by
    filter_upwards [Measure.ae_ae_of_ae_prod bF] with x bx
    have bi : ∀ᵐ y ∂μ.restrict X, 0 ≤ F (x,y) ∧ F (x,y) ≤ 1 := ae_restrict_of_ae bx
    have hi := (LowSupportAnalysis.unit_integrable_ae
      (hF.comp (measurable_const.prodMk measurable_id)) bx).restrict (s := X)
    refine ⟨integral_nonneg_of_ae (bi.mono fun _ h => h.1),?_⟩
    have hh := integral_mono_ae hi (integrable_const (1:ℝ)) (bi.mono fun _ h => h.2)
    have hmass : μ.real X ≤ 1 := measureReal_le_one
    simpa using hh.trans (by simpa using hmass)
  have bp : ∀ᵐ x ∂μ, 0 ≤ A x*(∫ y in X, F (x,y) ∂μ) ∧ A x*(∫ y in X, F (x,y) ∂μ) ≤ 1 := by
    filter_upwards [bA,bb] with x ax bx
    exact LowSupportAnalysis.mul_unit ax bx
  exact (integral_eq_zero_iff_of_nonneg_ae (bp.mono fun _ h => h.1)
    (LowSupportAnalysis.unit_integrable_ae (hA.mul hm) bp)).mp hz'
end ThirdsFivePathFactor
end JigBundleModule73

/- Inlined module ThirdsTensorAE; original SHA256 bef45f67472a47a507d6c83eaac771468caba90287b3c815d17a184b8aa4ba83 -/
section JigBundleModule74
open MeasureTheory
namespace ThirdsTensorAE
open ThirdsFivePathFactor
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma bounds (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (bg : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ tensor f g p ∧ tensor f g p ≤ 1 := by
  have hm : Measurable (tensor f g) := by unfold tensor; fun_prop
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const))).mpr
  filter_upwards [bf] with x bx
  filter_upwards [bg] with y by'
  exact LowSupportAnalysis.mul_unit bx by'
lemma congr_left (f f' g : Ω → ℝ) (hf : Measurable f) (hf' : Measurable f') (hg : Measurable g)
    (he : f =ᵐ[μ] f') : tensor f g =ᵐ[μ.prod μ] tensor f' g := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by unfold tensor; fun_prop)
    (by unfold tensor; fun_prop))).mpr
  filter_upwards [he] with x hx
  exact Filter.Eventually.of_forall (fun y => by change f x*g y=f' x*g y; rw [hx])
end ThirdsTensorAE
end JigBundleModule74

/- Inlined module ThirdsRankOneUnique; original SHA256 538aae8ac7800a41e1384bf85658dc662de627931a344627b9aeb2df7d2ef49c -/
section JigBundleModule75
open MeasureTheory
namespace ThirdsRankOneUnique
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma signed_row_alignment (r s : Ω → ℝ) (a b : ℝ)
    (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1)
    (he : ∀ᵐ y ∂μ, a*r y=b*s y) :
    (r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun y => -s y)) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · left; filter_upwards [he] with y hy; rw [ha,hb] at hy; nlinarith
  · right; filter_upwards [he] with y hy; rw [ha,hb] at hy; nlinarith
  · right; filter_upwards [he] with y hy; rw [ha,hb] at hy; nlinarith
  · left; filter_upwards [he] with y hy; rw [ha,hb] at hy; nlinarith
lemma unique_anchor (C : Ω × Ω → ℝ) (r s : Ω → ℝ) (e f : ℝ)
    (he : e=1 ∨ e= -1) (hf : f=1 ∨ f= -1)
    (rb : ∀ᵐ x ∂μ, r x=1 ∨ r x= -1) (sb : ∀ᵐ x ∂μ, s x=1 ∨ s x= -1)
    (hCr : C =ᵐ[μ.prod μ] (fun p => (1+e*r p.1*r p.2)/2))
    (hCs : C =ᵐ[μ.prod μ] (fun p => (1+f*s p.1*s p.2)/2)) :
    (r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun y => -s y)) := by
  have hp : ∀ᵐ p ∂μ.prod μ, (e*r p.1)*r p.2=(f*s p.1)*s p.2 := by
    filter_upwards [hCr,hCs] with p h1 h2
    linarith
  obtain ⟨x,hrx,hsx,hrow⟩ := (rb.and (sb.and (Measure.ae_ae_of_ae_prod hp))).exists
  have ha : e*r x=1 ∨ e*r x= -1 := by rcases he with h|h <;> rcases hrx with h'|h' <;> simp [h,h']
  have hb : f*s x=1 ∨ f*s x= -1 := by rcases hf with h|h <;> rcases hsx with h'|h' <;> simp [h,h']
  exact signed_row_alignment μ r s (e*r x) (f*s x) ha hb hrow
end ThirdsRankOneUnique
end JigBundleModule75

/- Inlined module ThirdsAENormalizedAnchor; original SHA256 8ca60f1222a13372f49feb4bfcc11c46fa91165e3a90b301b2dbc81e0c1382ab -/
section JigBundleModule76
open MeasureTheory
namespace ThirdsAENormalizedAnchor
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma normalized_anchor_ae (C D : Ω × Ω → ℝ) (r s : Ω → ℝ)
    (hC : Measurable C) (hD : Measurable D) (hr : Measurable r) (hs : Measurable s)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (hCD : ∀ᵐ p ∂μ.prod μ, C p+D p=1)
    (br : ∀ x, -1 ≤ r x ∧ r x ≤ 1) (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1)
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (mr : ∫ x, r x ∂μ=0) (ms : ∫ x, s x ∂μ=0)
    (hz₁ : cycle4 μ C D (anchor s) (anchor r)=0)
    (hz₂ : cycle4 μ C (anchor r) D (anchor s)=0) :
    ∃ S : Set Ω, ∃ e : ℝ, MeasurableSet S ∧ μ.real S=(1:ℝ)/2 ∧
      (e=1 ∨ e= -1) ∧ (r =ᵐ[μ] (fun x => 2*oneSet S x-1)) ∧
      ((r =ᵐ[μ] s) ∨ (r =ᵐ[μ] (fun x => -s x))) ∧
      (C =ᵐ[μ.prod μ] (fun p => (1+e*r p.1*r p.2)/2)) := by
  let K := symclip C
  have hK : Measurable K := measurable_symclip hC
  have bK := symclip_bounds C
  have eK : K =ᵐ[μ.prod μ] C := symclip_eq_ae μ C bC sC
  have eD : (fun p => 1-K p) =ᵐ[μ.prod μ] D := by
    filter_upwards [eK,hCD] with p hp hd
    change K p=C p at hp
    change 1-K p=D p
    linarith
  have rK : ∀ᵐ x ∂μ, ∫ y, K (x,y) ∂μ=(1:ℝ)/2 := by
    filter_upwards [Measure.ae_ae_of_ae_prod eK,hrow] with x hx hd
    rw [integral_congr_ae hx,hd]
  have hzK₁ : cycle4 μ K (fun p => 1-K p) (anchor s) (anchor r)=0 := by
    rw [cycle4_congr μ eK eD Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl,hz₁]
  have hzK₂ : cycle4 μ K (anchor r) (fun p => 1-K p) (anchor s)=0 := by
    rw [cycle4_congr μ eK Filter.EventuallyEq.rfl eD Filter.EventuallyEq.rfl,hz₂]
  obtain ⟨S,e,hS,mS,he,hrep,hrs,hkernel⟩ := ThirdsNormalizedAnchor.normalized_anchor μ K r s
    hK hr hs bK br bs (fun x y => symclip_symm C (x,y)) rK mr ms hzK₁ hzK₂
  exact ⟨S,e,hS,mS,he,hrep,hrs,eK.symm.trans hkernel⟩
end ThirdsAENormalizedAnchor
end JigBundleModule76

/- Inlined module ThirdsSelectedCenter; original SHA256 cab6e07820ab25ffce001e1d997b98768a08f072fb7005d5c9c68c2b479a523c -/
section JigBundleModule77
open MeasureTheory
namespace ThirdsSelectedCenter
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
def RowGood (W : Fin 6 → Ω × Ω → ℝ) (x : Ω) : Prop :=
  (∀ i, ∀ᵐ y ∂μ, 0 ≤ W i (x,y) ∧ W i (x,y) ≤ 1 ∧ W i (y,x)=W i (x,y)) ∧
  (∀ᵐ y ∂μ, ∑ i, W i (x,y)=1)
lemma rowGood_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hs : ∀ i, ∀ᵐ p ∂μ.prod μ, W i p=W i (p.2,p.1))
    (hp : ∀ᵐ p ∂μ.prod μ, ∑ i, W i p=1) : ∀ᵐ x ∂μ, RowGood μ W x := by
  have hrows : ∀ i, ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      0 ≤ W i (x,y) ∧ W i (x,y) ≤ 1 ∧ W i (y,x)=W i (x,y) := by
    intro i
    apply Measure.ae_ae_of_ae_prod (p := fun p : Ω × Ω =>
      0 ≤ W i p ∧ W i p ≤ 1 ∧ W i (p.2,p.1)=W i p)
    filter_upwards [hb i,hs i] with p hb hs
    exact ⟨hb.1,hb.2,hs.symm⟩
  filter_upwards [ae_all_iff.mpr hrows,Measure.ae_ae_of_ae_prod hp] with x hx hp
  exact ⟨hx,hp⟩
lemma selected_center (W : Fin 6 → Ω × Ω → ℝ) (hm : ∀ i, Measurable (W i))
    (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d)
    (u : Ω) (hu : RowGood μ W u) (i j : Fin 6) (hij : i ≠ j)
    (mi : act μ (W i) (oneSet S) u=d) (mj : act μ (W j) (oneSet S) u=d) :
    ∃ r : Ω → ℝ, Measurable r ∧ (∀ x, -1 ≤ r x ∧ r x ≤ 1) ∧
      (∫ x, r x ∂ProbabilityTheory.cond μ S)=0 ∧
      ((fun x => W i (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2)) ∧
      ((fun x => W j (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2)) ∧
      (ThirdsCanonicalAnchors.bridge W i j u =ᵐ[(ProbabilityTheory.cond μ S).prod
        (ProbabilityTheory.cond μ S)] anchor r) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd mS
  have ha : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hrow := ae_all_iff.mpr hu.1
  have hcap : ∀ᵐ y ∂ν, W i (u,y)+W j (u,y) ≤ 1 := by
    filter_upwards [hrow.filter_mono ha.ae_le,hu.2.filter_mono ha.ae_le] with y hy hp
    have hh : (∑ c ∈ ({i,j} : Finset (Fin 6)), W c (u,y)) ≤ ∑ c, W c (u,y) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => (hy c).1)
    simpa [Finset.sum_pair hij,hp] using hh
  have bi : ∀ᵐ y ∂ν, 0 ≤ W i (u,y) ∧ W i (u,y) ≤ 1 :=
    (hu.1 i).filter_mono ha.ae_le |>.mono (fun _ h => ⟨h.1,h.2.1⟩)
  have bj : ∀ᵐ y ∂ν, 0 ≤ W j (u,y) ∧ W j (u,y) ≤ 1 :=
    (hu.1 j).filter_mono ha.ae_le |>.mono (fun _ h => ⟨h.1,h.2.1⟩)
  have mass (c : Fin 6) (hc : act μ (W c) (oneSet S) u=d) :
      (∫ x, W c (u,x) ∂ν)=(1:ℝ)/2 := by
    rw [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ (W c) S hS] at hc
    rw [ThirdsNormalizedRestriction.conditional_integral μ S,mS,hc]
    field_simp
    <;> nlinarith
  obtain ⟨r,hr,br,mr,er,ej⟩ := ThirdsRowCentering.complementary_center ν
    (fun x => W i (u,x)) (fun x => W j (u,x)) (by fun_prop) (by fun_prop)
    bi bj hcap (mass i mi) (mass j mj)
  refine ⟨r,hr,br,mr,er,ej,?_⟩
  apply ThirdsRowCentering.bridge_centered ν W hm i j u r hr er ej
  · exact ((hu.1 i).filter_mono ha.ae_le).mono (fun _ h => h.2.2)
  · exact ((hu.1 j).filter_mono ha.ae_le).mono (fun _ h => h.2.2)
end ThirdsSelectedCenter
end JigBundleModule77

/- Inlined module ThirdsActualFivePath; original SHA256 4fafc12725017e176375dccc0d684d762b5fb8602acde8d55c1758a00aa907e2 -/
section JigBundleModule78
open MeasureTheory
namespace ThirdsActualFivePath
open FourColorKernels TwoPairHalfSetOperator ThirdsFivePathFactor ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma exclusion (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (X Z M : Set Ω) (hX : MeasurableSet X) (hM : μ M ≠ 0)
    (hclique : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hroot : ∀ᵐ z ∂μ, z∈Z → (fun x => W 4 (z,x)) =ᵐ[μ] oneSet X)
    (hanchor : ∀ᵐ v ∂μ, v∈M →
      (0 < ∫ x in X, W 2 (x,v) ∂μ) ∧ (0 < ∫ x in X, W 3 (v,x) ∂μ))
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ z ∂μ, z∈Z → ∀ᵐ x ∂μ, W 5 (z,x)*(∫ y in X, W 0 (x,y) ∂μ)=0 := by
  have hzero := ThirdsOrderedAnchors.adjacent_zero_ae μ W hW bW hz
  have hRG := rowGood_ae μ W bW sW hpart
  have hI := oneSet_measurable X hX
  have bI : ∀ᵐ x ∂μ, 0 ≤ oneSet X x ∧ oneSet X x ≤ 1 := Filter.Eventually.of_forall (oneSet_bounds X)
  have hle : ∀ᵐ p ∂μ.prod μ, 0 ≤ tensor (oneSet X) (oneSet X) p ∧
      tensor (oneSet X) (oneSet X) p ≤ W 1 p := by
    filter_upwards [bW 1,hclique] with p bp cp
    constructor
    · exact mul_nonneg (oneSet_bounds X p.1).1 (oneSet_bounds X p.2).1
    · by_cases hx : p.1∈X
      · rw [cp hx]; simp [tensor,oneSet,hx]
      · simpa [tensor,oneSet,hx] using bp.1
  filter_upwards [hzero,hRG,hroot] with z hz0 hgz hrz
  intro hzz
  have hv : ∀ᵐ v ∂μ, RowGood μ W v ∧
      (v∈M → (0 < ∫ x in X, W 2 (x,v) ∂μ) ∧ (0 < ∫ x in X, W 3 (v,x) ∂μ)) ∧
      cycle4 μ (W 0) (W 1) (ThirdsCanonicalAnchors.path W 2 3 false v)
        (ThirdsCanonicalAnchors.path W 4 5 false z)=0 := by
    filter_upwards [hRG,hanchor,hz0] with v hg ha hz
    exact ⟨hg,ha,hz⟩
  obtain ⟨v,hvm,hgv,hav,hzv⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hM (ae_restrict_of_ae hv)
  let D := fun x => W 2 (x,v)
  let E := fun x => W 3 (v,x)
  let A := fun x => W 5 (z,x)
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hE : Measurable E := by dsimp [E]; fun_prop
  have hA : Measurable A := by dsimp [A]; fun_prop
  have bD : ∀ᵐ x ∂μ, 0 ≤ D x ∧ D x ≤ 1 := by
    filter_upwards [hgv.1 2] with x hx
    dsimp [D]; rw [hx.2.2]; exact ⟨hx.1,hx.2.1⟩
  have bE : ∀ᵐ x ∂μ, 0 ≤ E x ∧ E x ≤ 1 := (hgv.1 3).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have bA : ∀ᵐ x ∂μ, 0 ≤ A x ∧ A x ≤ 1 := (hgz.1 5).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have hcin : (fun x => W 4 (x,z)) =ᵐ[μ] oneSet X := by
    filter_upwards [hgz.1 4,hrz hzz] with x hx hy
    rw [hx.2.2,hy]
  have ek : ThirdsCanonicalAnchors.path W 4 5 false z =ᵐ[μ.prod μ] tensor (oneSet X) A :=
    ThirdsTensorAE.congr_left μ (fun x => W 4 (x,z)) (oneSet X) A (by fun_prop) hI hA hcin
  have hz' : cycle4 μ (W 0) (W 1) (tensor D E) (tensor (oneSet X) A)=0 := by
    rw [← cycle4_congr μ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl ek]
    exact hzv
  have hlow : cycle4 μ (W 0) (tensor (oneSet X) (oneSet X)) (tensor D E) (tensor (oneSet X) A)=0 :=
    ThirdsCycle4Restrict.middle_zero μ (W 0) (W 1) (tensor (oneSet X) (oneSet X))
      (tensor D E) (tensor (oneSet X) A) (hW 0) (hW 1) (by unfold tensor; fun_prop)
      (by unfold tensor; fun_prop) (by unfold tensor; fun_prop) (bW 0) (bW 1)
      (ThirdsTensorAE.bounds μ D E hD hE bD bE) (ThirdsTensorAE.bounds μ (oneSet X) A hI hA bI bA) hle hz'
  exact ThirdsFivePathFactor.positive_forces_zero μ (W 0) X hX D E A (hW 0) hA (bW 0) bA
    (hav hvm).1 (hav hvm).2 hlow
end ThirdsActualFivePath
end JigBundleModule78

/- Inlined module ThirdsIndependentAnchorColumns; original SHA256 b64c504ec20ec1ce4db58a6b6e9124dacf441118c32f82f1b633b6015dfef8a6 -/
section JigBundleModule79
open MeasureTheory
namespace ThirdsIndependentAnchorColumns
open ThirdsCanonicalAnchors ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma independent_binary (ν : Measure Ω) (f g : Ω → ℝ)
    (hpart : ∀ᵐ z ∂ν, f z + g z = 1)
    (hz : ∀ᵐ z₀ ∂ν, ∀ᵐ z₁ ∂ν, f z₁ * g z₀ = 0) :
    (f =ᵐ[ν] fun _ => 0) ∨ (f =ᵐ[ν] fun _ => 1) := by
  by_cases hf : f =ᵐ[ν] fun _ => 0
  · exact Or.inl hf
  · right
    have hg : g =ᵐ[ν] fun _ => 0 := by
      filter_upwards [hz] with z hzz
      by_contra hn
      apply hf
      filter_upwards [hzz] with y hy
      exact (mul_eq_zero.mp hy).resolve_right hn
    filter_upwards [hpart,hg] with z hp hg
    simpa [hg] using hp

lemma four_full_edges (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (Z X Y T : Set Ω) (pX : μ X ≠ 0) (pY : μ Y ≠ 0) (pT : μ T ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈X → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Y → W 1 p=1)
    (f2 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈T → W 2 p=1)
    (f3 : ∀ᵐ p ∂μ.prod μ, p.1∈T → p.2∈Z → W 3 p=1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ r ∂μ, ∀ᵐ z₀ ∂μ, z₀∈Z → ∀ᵐ z₁ ∂μ, z₁∈Z →
      W 4 (z₁,r) * W 5 (r,z₀)=0 := by
  have hz4 := ThirdsOrderedAnchors.adjacent_zero_ae μ W hW bW hz
  have hg := rowGood_ae μ W bW sW hpart
  have hf0 := Measure.ae_ae_of_ae_prod f0
  have hf1 := Measure.ae_ae_of_ae_prod f1
  have hf2 := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae f2)
  have hf3 := Measure.ae_ae_of_ae_prod f3
  filter_upwards [hz4,hg] with r hr hgr
  have hv : ∀ᵐ v ∂μ, RowGood μ W v ∧
      (∀ᵐ y ∂μ, y∈Y → v∈T → W 2 (y,v)=1) ∧
      (∀ᵐ z ∂μ, v∈T → z∈Z → W 3 (v,z)=1) ∧
      cycle4 μ (W 0) (W 1) (path W 2 3 false v) (path W 4 5 false r)=0 := by
    filter_upwards [hg,hf2,hf3,hr] with v gv h2 h3 h0
    exact ⟨gv,h2,h3,h0⟩
  obtain ⟨v,hvT,hgv,h2,h3,hvzero⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae pT (ae_restrict_of_ae hv)
  have bp (i j : Fin 6) (u : Ω) (gu : RowGood μ W u) :
      ∀ᵐ p ∂μ.prod μ, 0 ≤ path W i j false u p ∧ path W i j false u p ≤ 1 := by
    apply ThirdsTensorAE.bounds μ (fun x => W i (x,u)) (fun y => W j (u,y))
      (by fun_prop) (by fun_prop)
    · filter_upwards [gu.1 i] with x hx
      rw [hx.2.2]
      exact ⟨hx.1,hx.2.1⟩
    · exact (gu.1 j).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have hh := (ThirdsCycle4ZeroAE.zero_iff μ (W 0) (W 1)
    (path W 2 3 false v) (path W 4 5 false r) (hW 0) (hW 1)
    (path_measurable W hW 2 3 false v) (path_measurable W hW 4 5 false r)
    (bW 0) (bW 1) (bp 2 3 v hgv) (bp 4 5 r hgr)).mp hvzero
  filter_upwards [hh,hf0] with z₀ hz₀ h0
  intro hz₀Z
  have hxx : ∀ᵐ x ∂μ, (∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      W 0 (z₀,x)*W 1 (x,y)*path W 2 3 false v (y,z)*path W 4 5 false r (z,z₀)=0) ∧
      (z₀∈Z → x∈X → W 0 (z₀,x)=1) ∧
      (∀ᵐ y ∂μ, x∈X → y∈Y → W 1 (x,y)=1) := by
    filter_upwards [hz₀,h0,hf1] with x hx h0x h1x
    exact ⟨hx,h0x,h1x⟩
  obtain ⟨x,hxX,hxz,h0x,h1x⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae pX (ae_restrict_of_ae hxx)
  have hyy : ∀ᵐ y ∂μ, (∀ᵐ z ∂μ,
      W 0 (z₀,x)*W 1 (x,y)*path W 2 3 false v (y,z)*path W 4 5 false r (z,z₀)=0) ∧
      (x∈X → y∈Y → W 1 (x,y)=1) ∧ (y∈Y → v∈T → W 2 (y,v)=1) := by
    filter_upwards [hxz,h1x,h2] with y hy h1y h2y
    exact ⟨hy,h1y,h2y⟩
  obtain ⟨y,hyY,hyz,h1y,h2y⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae pY (ae_restrict_of_ae hyy)
  filter_upwards [hyz,h3] with z₁ hzz h3z
  intro hz₁Z
  simpa [path,h0x hz₀Z hxX,h1y hxX hyY,h2y hyY hvT,h3z hvT hz₁Z] using hzz

lemma binary_columns (Z : Set Ω) (hZ : MeasurableSet Z)
    (A F : Ω × Ω → ℝ)
    (hp : ∀ᵐ r ∂μ, ∀ᵐ z ∂μ, z ∈ Z → A (z,r) + F (r,z) = 1)
    (hz : ∀ᵐ r ∂μ, ∀ᵐ z₀ ∂μ, z₀ ∈ Z → ∀ᵐ z₁ ∂μ, z₁ ∈ Z →
      A (z₁,r) * F (r,z₀) = 0) :
    ∀ᵐ r ∂μ, ((fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 0) ∨
      ((fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 1) := by
  filter_upwards [hp,hz] with r hp hz
  apply independent_binary (μ.restrict Z) (fun z => A (z,r)) (fun z => F (r,z))
  · exact (ae_restrict_iff' hZ).mpr hp
  · apply (ae_restrict_iff' hZ).mpr
    filter_upwards [hz] with z₀ hz₀
    intro hz₀Z
    exact (ae_restrict_iff' hZ).mpr (hz₀ hz₀Z)

end ThirdsIndependentAnchorColumns
end JigBundleModule79

/- Inlined module ThirdsOneMixingHZero; original SHA256 940d043e4ac6ba9128cfaa53fcd65b37f7361f719eeeb3c1180ba299d8b933a1 -/
section JigBundleModule80
open MeasureTheory
namespace ThirdsOneMixingHZero
open ThirdsCanonicalAnchors ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma four_full_path (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (Z X Y T U : Set Ω) (pX : μ X ≠ 0) (pY : μ Y ≠ 0) (pT : μ T ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈X → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Y → W 1 p=1)
    (f2 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈T → W 2 p=1)
    (f3 : ∀ᵐ p ∂μ.prod μ, p.1∈T → p.2∈U → W 3 p=1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ r ∂μ, ∀ᵐ z₀ ∂μ, z₀∈Z → ∀ᵐ z₁ ∂μ, z₁∈U →
      W 4 (z₁,r) * W 5 (r,z₀)=0 := by
  have hz4 := ThirdsOrderedAnchors.adjacent_zero_ae μ W hW bW hz
  have hg := rowGood_ae μ W bW sW hpart
  have hf0 := Measure.ae_ae_of_ae_prod f0
  have hf1 := Measure.ae_ae_of_ae_prod f1
  have hf2 := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae f2)
  have hf3 := Measure.ae_ae_of_ae_prod f3
  filter_upwards [hz4,hg] with r hr hgr
  have hv : ∀ᵐ v ∂μ, RowGood μ W v ∧
      (∀ᵐ y ∂μ, y∈Y → v∈T → W 2 (y,v)=1) ∧
      (∀ᵐ z ∂μ, v∈T → z∈U → W 3 (v,z)=1) ∧
      cycle4 μ (W 0) (W 1) (path W 2 3 false v) (path W 4 5 false r)=0 := by
    filter_upwards [hg,hf2,hf3,hr] with v gv h2 h3 h0
    exact ⟨gv,h2,h3,h0⟩
  obtain ⟨v,hvT,hgv,h2,h3,hvzero⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae pT (ae_restrict_of_ae hv)
  have bp (i j : Fin 6) (u : Ω) (gu : RowGood μ W u) :
      ∀ᵐ p ∂μ.prod μ, 0 ≤ path W i j false u p ∧ path W i j false u p ≤ 1 := by
    apply ThirdsTensorAE.bounds μ (fun x => W i (x,u)) (fun y => W j (u,y))
      (by fun_prop) (by fun_prop)
    · filter_upwards [gu.1 i] with x hx
      rw [hx.2.2]
      exact ⟨hx.1,hx.2.1⟩
    · exact (gu.1 j).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have hh := (ThirdsCycle4ZeroAE.zero_iff μ (W 0) (W 1)
    (path W 2 3 false v) (path W 4 5 false r) (hW 0) (hW 1)
    (path_measurable W hW 2 3 false v) (path_measurable W hW 4 5 false r)
    (bW 0) (bW 1) (bp 2 3 v hgv) (bp 4 5 r hgr)).mp hvzero
  filter_upwards [hh,hf0] with z₀ hz₀ h0
  intro hz₀Z
  have hxx : ∀ᵐ x ∂μ, (∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      W 0 (z₀,x)*W 1 (x,y)*path W 2 3 false v (y,z)*path W 4 5 false r (z,z₀)=0) ∧
      (z₀∈Z → x∈X → W 0 (z₀,x)=1) ∧
      (∀ᵐ y ∂μ, x∈X → y∈Y → W 1 (x,y)=1) := by
    filter_upwards [hz₀,h0,hf1] with x hx h0x h1x
    exact ⟨hx,h0x,h1x⟩
  obtain ⟨x,hxX,hxz,h0x,h1x⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae pX (ae_restrict_of_ae hxx)
  have hyy : ∀ᵐ y ∂μ, (∀ᵐ z ∂μ,
      W 0 (z₀,x)*W 1 (x,y)*path W 2 3 false v (y,z)*path W 4 5 false r (z,z₀)=0) ∧
      (x∈X → y∈Y → W 1 (x,y)=1) ∧ (y∈Y → v∈T → W 2 (y,v)=1) := by
    filter_upwards [hxz,h1x,h2] with y hy h1y h2y
    exact ⟨hy,h1y,h2y⟩
  obtain ⟨y,hyY,hyz,h1y,h2y⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae pY (ae_restrict_of_ae hyy)
  filter_upwards [hyz,h3] with z₁ hzz h3z
  intro hz₁Z
  simpa [path,h0x hz₀Z hxX,h1y hxX hyY,h2y hyY hvT,h3z hvT hz₁Z] using hzz


lemma integrate_path (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (Z X T Y : Set Ω) (hY : MeasurableSet Y) (pX : μ X ≠ 0) (pT : μ T ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈X → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈X → W 1 p=1)
    (f2 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈T → W 2 p=1)
    (f3 : ∀ᵐ p ∂μ.prod μ, p.1∈T → p.2∈Y → W 3 p=1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) :
    ∀ᵐ h ∂μ, ∀ᵐ z ∂μ, z∈Z → W 5 (h,z)*(∫ y in Y, W 4 (h,y) ∂μ)=0 := by
  have hp := four_full_path μ W hW bW sW hpart Z X X T Y pX pX pT f0 f1 f2 f3 hz
  have hs := Measure.ae_ae_of_ae_prod (sW 4)
  filter_upwards [hp,hs] with h hh sh
  filter_upwards [hh] with z hz
  intro hzZ
  have he : ∀ᵐ y ∂μ.restrict Y, W 5 (h,z)*W 4 (h,y)=0 := by
    apply (ae_restrict_iff' hY).mpr
    filter_upwards [hz hzZ,sh] with y hy sy
    intro hyY
    have eq : W 4 (h,y)=W 4 (y,h) := sy
    rw [eq,mul_comm]
    exact hy hyY
  rw [← integral_const_mul,integral_congr_ae he,integral_zero]

lemma two_split (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (Z X I₀ I₁ Y : Set Ω) (hY : MeasurableSet Y) (pX : μ X ≠ 0)
    (pI : μ I₀ ≠ 0 ∨ μ I₁ ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈X → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈X → W 1 p=1)
    (f20 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈I₀ → W 2 p=1)
    (f30 : ∀ᵐ p ∂μ.prod μ, p.1∈I₀ → p.2∈Y → W 3 p=1)
    (f21 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈I₁ → W 3 p=1)
    (f31 : ∀ᵐ p ∂μ.prod μ, p.1∈I₁ → p.2∈Y → W 2 p=1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0)
    (hz' : LowSupportCycle.cycleNested (μ := μ) (fun i => W ((Equiv.swap (2:Fin 6) 3) i))=0) :
    ∀ᵐ h ∂μ, ∀ᵐ z ∂μ, z∈Z → W 5 (h,z)*(∫ y in Y, W 4 (h,y) ∂μ)=0 := by
  rcases pI with pI | pI
  · exact integrate_path μ W hW bW sW hpart Z X I₀ Y hY pX pI f0 f1 f20 f30 hz
  · let σ : Equiv.Perm (Fin 6) := Equiv.swap 2 3
    let V := fun i => W (σ i)
    have hp : ∀ᵐ p ∂μ.prod μ, ∑ c, V c p=1 := by
      filter_upwards [hpart] with p hp
      dsimp [V]
      rw [Equiv.sum_comp σ (fun c => W c p)]
      exact hp
    have e0 : V 0=W 0 := by simp [V,σ,Equiv.swap_apply_def]
    have e1 : V 1=W 1 := by simp [V,σ,Equiv.swap_apply_def]
    have e2 : V 2=W 3 := by simp [V,σ]
    have e3 : V 3=W 2 := by simp [V,σ]
    have e4 : V 4=W 4 := by simp [V,σ,Equiv.swap_apply_def]
    have e5 : V 5=W 5 := by simp [V,σ,Equiv.swap_apply_def]
    have hh := integrate_path μ V (fun i => hW (σ i)) (fun i => bW (σ i))
      (fun i => sW (σ i)) hp Z X I₁ Y hY pX pI
      (by simpa only [e0] using f0) (by simpa only [e1] using f1)
      (by simpa only [e2] using f21) (by simpa only [e3] using f31) hz'
    simpa only [e4,e5] using hh

lemma combine (A D E : Ω × Ω → ℝ) (Z H Y : Set Ω) (d : ℝ) (hd : d ≠ 0)
    (he : ∀ᵐ h ∂μ, ∀ᵐ z ∂μ, z∈Z → A (h,z)*(∫ y in Y, E (h,y) ∂μ)=0)
    (hf : ∀ᵐ h ∂μ, ∀ᵐ z ∂μ, z∈Z → A (h,z)*(∫ y in Y, D (h,y) ∂μ)=0)
    (hm : ∀ᵐ h ∂μ, h∈H → (∫ y in Y, D (h,y) ∂μ)+(∫ y in Y, E (h,y) ∂μ)=d) :
    ∀ᵐ h ∂μ, h∈H → ∀ᵐ z ∂μ, z∈Z → A (h,z)=0 := by
  filter_upwards [he,hf,hm] with h he hf hm
  intro hh
  filter_upwards [he,hf] with z he hf
  intro hz
  have hp : A (h,z)*d=0 := by rw [← hm hh,mul_add,he hz,hf hz]; ring
  exact (mul_eq_zero.mp hp).resolve_right hd

lemma positive_split (I₀ I₁ : Set Ω) (d : ℝ) (hd : 0 < d)
    (hm : μ.real I₀ + μ.real I₁ = d) : μ I₀ ≠ 0 ∨ μ I₁ ≠ 0 := by
  by_cases h0 : μ I₀=0
  · right
    intro h1
    have hz : d=0 := by simpa [measureReal_def,h0,h1] using hm.symm
    linarith
  · exact Or.inl h0

lemma combine_on_rectangle (A D E : Ω × Ω → ℝ) (hA : Measurable A)
    (sA : ∀ᵐ p ∂μ.prod μ, A p=A (p.2,p.1))
    (Z H Y : Set Ω) (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (d : ℝ) (hd : d ≠ 0)
    (he : ∀ᵐ h ∂μ, ∀ᵐ z ∂μ, z∈Z → A (h,z)*(∫ y in Y, E (h,y) ∂μ)=0)
    (hf : ∀ᵐ h ∂μ, ∀ᵐ z ∂μ, z∈Z → A (h,z)*(∫ y in Y, D (h,y) ∂μ)=0)
    (hm : ∀ᵐ h ∂μ, h∈H → (∫ y in Y, D (h,y) ∂μ)+(∫ y in Y, E (h,y) ∂μ)=d) :
    ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → A p=0 := by
  have hh := combine μ A D E Z H Y d hd he hf hm
  have hp : ∀ᵐ p ∂μ.prod μ, p.1∈H → p.2∈Z → A p=0 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [hh] with h hh
    by_cases hhh : h∈H
    · filter_upwards [hh hhh] with z hz
      exact fun _ => hz
    · exact Filter.Eventually.of_forall (fun z hx => (hhh hx).elim)
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp
  filter_upwards [hs,sA] with p hp sp
  intro hz hh
  rw [sp]
  exact hp hh hz

end ThirdsOneMixingHZero
end JigBundleModule80

/- Inlined module D10FullCycle; original SHA256 72940e74d27ad9f8166a880ca57d4fdd747af7ddee326da8e3b9ffd8d111fc39 -/
section JigBundleModule81
open MeasureTheory
namespace D10FullCycle
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma impossible (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (A B C D E F : Set Ω)
    (pA : μ A ≠ 0) (pB : μ B ≠ 0) (pC : μ C ≠ 0)
    (pD : μ D ≠ 0) (pE : μ E ≠ 0) (pF : μ F ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈A → p.2∈B → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈B → p.2∈C → W 1 p=1)
    (f2 : ∀ᵐ p ∂μ.prod μ, p.1∈C → p.2∈D → W 2 p=1)
    (f3 : ∀ᵐ p ∂μ.prod μ, p.1∈D → p.2∈E → W 3 p=1)
    (f4 : ∀ᵐ p ∂μ.prod μ, p.1∈E → p.2∈F → W 4 p=1)
    (f5 : ∀ᵐ p ∂μ.prod μ, p.1∈F → p.2∈A → W 5 p=1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W=0) : False := by
  have hh := ThirdsOneMixingHZero.four_full_path μ W hW bW sW hpart A B C D E pB pC pD f0 f1 f2 f3 hz
  have h4 := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae f4)
  have h5 := Measure.ae_ae_of_ae_prod f5
  obtain ⟨r,hrF,hr,h4r,h5r⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pF
    (ae_restrict_of_ae (hh.and (h4.and h5)))
  obtain ⟨a,haA,ha,h5a⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pA
    (ae_restrict_of_ae (hr.and h5r))
  obtain ⟨e,heE,he,h4e⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pE
    (ae_restrict_of_ae ((ha haA).and h4r))
  have zero := he heE
  have e4 : W 4 (e,r)=1 := h4e heE hrF
  rw [e4,h5a hrF haA] at zero
  norm_num at zero
end D10FullCycle
end JigBundleModule81

/- Inlined module D10BlockExclusion; original SHA256 11cb5cabcdd2836097ff089ba7508e099f08f47028358e0f7bc7e120a4669efa -/
section JigBundleModule82
open MeasureTheory
namespace D10BlockExclusion
open D10BlockPropagationCore
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma impossible (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0)
    (T : Fin 6 → Set Ω) (pT : ∀ i, μ (T i) ≠ 0)
    (x : Matrix) (nn : ∀ c i j, 0 ≤ x c i j)
    (symm : ∀ c i j, x c i j = x c j i)
    (part : ∀ i j, ∑ c, x c i j = 1) (rows : ∀ c i, ∑ j, x c i j = 1)
    (r : Fin 6) (root : ∀ c j, x c r j = if c=j then 1 else 0)
    (forbidden : ∀ i j c, i≠j → c≠i → c≠j → ¬palette i j c → x c i j=0)
    (full : ∀ c i j, x c i j=1 → ∀ᵐ p ∂μ.prod μ, p.1∈T i → p.2∈T j → W c p=1) : False := by
  have hs := D10BlockInitial.support x nn symm rows r root forbidden
  obtain ⟨a,b,c,d,e,f,σ,h0,h1,h2,h3,h4,h5⟩ :=
    D10BlockPropagation.rainbow x nn symm part rows r hs
  have hp : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]
    exact hp
  exact D10FullCycle.impossible μ (fun c => W (σ c))
    (fun c => hW (σ c)) (fun c => bW (σ c)) (fun c => sW (σ c)) hp
    (T a) (T b) (T c) (T d) (T e) (T f) (pT a) (pT b) (pT c) (pT d) (pT e) (pT f)
    (full _ _ _ h0) (full _ _ _ h1) (full _ _ _ h2)
    (full _ _ _ h3) (full _ _ _ h4) (full _ _ _ h5) (hz σ)
end D10BlockExclusion
end JigBundleModule82

/- Inlined module D10JointTwinExclusion; original SHA256 3cee3ad245cf33764641802f3b78029aef739fcf70d189ead563904c76711516 -/
section JigBundleModule83
open MeasureTheory
namespace D10JointTwinExclusion
open TwoPairHalfSetOperator D10BlockPropagationCore
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
/-- Under the displayed D10 palette, balanced symmetric six-color kernels with
zero rainbow six-cycle density have no joint indicator-twin set of mass 1/6. -/
lemma impossible (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (part : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (degree : ∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x,y) ∂μ)=(1:ℝ)/6)
    (cycles : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0)
    (triangles : ∀ i j c : Fin 6, i≠j → c≠i → c≠j → ¬palette i j c →
      (∫ z, ∫ x, ∫ y, W i (z,x)*W c (x,y)*W j (y,z) ∂μ ∂μ ∂μ)=0)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ.real S=(1:ℝ)/6)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (twins : ∀ c, ∀ᵐ x ∂μ.restrict S, (fun y => W c (x,y)) =ᵐ[μ] oneSet (T c)) : False := by
  have pS : μ S≠0 := by intro hz; simp [measureReal_def,hz] at mS
  have ⟨mT,hpart⟩ := D10TwinTargets.targets μ W ((1:ℝ)/6) degree part S pS T hT twins
  have mt : ∀ c, μ (T c)=μ S := by
    intro c
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp
    exact (mT c).trans mS.symm
  obtain ⟨r,hr⟩ := D10TwinInternal.internal μ W hW sW S hS (pos_iff_ne_zero.mpr pS) T hT mt hpart twins
  let x : Matrix := D10BlockIntegrals.block μ W T ((1:ℝ)/6)
  have root : ∀ c j, x c r j=if c=j then 1 else 0 :=
    D10BlockRoot.root μ W hW S hS T hT mT hpart twins r hr
  have forbidden : ∀ i j c, i≠j → c≠i → c≠j → ¬palette i j c → x c i j=0 := by
    intro i j c hij hci hcj hp
    have ht := (D10TriangleZeroAE.zero_iff μ (W i) (W c) (W j)
      (hW i) (hW c) (hW j) (bW i) (bW c) (bW j)).mp (triangles i j c hij hci hcj hp)
    have hz := D10TwinTriangle.zero_rectangle μ (W i) (W j) (W c) (hW c) (sW j)
      S (T i) (T j) (hT i) (hT j) pS (twins i) (twins j) ht
    exact D10BlockRoot.constant μ W T hT mT c i j 0 hz
  exact D10BlockExclusion.impossible μ W hW bW sW part cycles T
    (fun i hz => by have hm := mT i; simp [measureReal_def,hz] at hm) x
    (D10BlockIntegrals.nonneg μ W bW T ((1:ℝ)/6))
    (D10BlockRows.symmetry μ W sW T ((1:ℝ)/6))
    (D10BlockIntegrals.part μ W hW bW part T ((1:ℝ)/6) (by norm_num) mT)
    (D10BlockRows.rows μ W hW bW degree T hT mT hpart) r root forbidden
    (D10BlockIntegrals.full μ W hW bW T hT ((1:ℝ)/6) mT)
end D10JointTwinExclusion
end JigBundleModule83

/- Inlined module ThirdsCrossClique; original SHA256 ec0b13c9a7fce55979e3d43be1b860220287512a8611e98f9573b11a6f45bbea -/
section JigBundleModule84
open MeasureTheory
namespace ThirdsCrossClique
open TwoPairHalfSetOperator
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
noncomputable def cross (X : Set Ω) (p : Ω × Ω) : ℝ :=
  oneSet X p.1*(1-oneSet X p.2)+(1-oneSet X p.1)*oneSet X p.2
noncomputable def otherClique (X : Set Ω) (p : Ω × Ω) : ℝ := (1-oneSet X p.1)*(1-oneSet X p.2)
def mixed (f : Ω → ℝ) (p : Ω × Ω) : ℝ := f p.1*(1-f p.2)+(1-f p.1)*f p.2
lemma three_edge_product (X : Set Ω) (x y z t : Ω) :
    cross X (x,y)*otherClique X (y,z)*cross X (z,t)=
      (1-oneSet X y)*(1-oneSet X z)*oneSet X x*oneSet X t := by
  rcases oneSet_binary X x with hx|hx <;> rcases oneSet_binary X y with hy|hy <;>
    rcases oneSet_binary X z with hz|hz <;> rcases oneSet_binary X t with ht|ht <;>
    simp [cross,otherClique,hx,hy,hz,ht]
lemma cross_clique_cycle (X : Set Ω) (hX : MeasurableSet X) (mX : μ.real X=(1:ℝ)/2)
    (f : Ω → ℝ) (hf : Measurable f) (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) :
    cycle4 μ (cross X) (otherClique X) (cross X) (mixed f)=
      (1:ℝ)/4*(∫ x in X, ∫ t in X, f x*(1-f t)+(1-f x)*f t ∂μ ∂μ) := by
  have hi : Integrable (oneSet X) μ := LowSupportAnalysis.unit_integrable_ae (oneSet_measurable X hX)
    (Filter.Eventually.of_forall (oneSet_bounds X))
  have mi : (∫ x, oneSet X x ∂μ)=(1:ℝ)/2 := by simpa [oneSet,integral_indicator hX] using mX
  have mg : (∫ x, 1-oneSet X x ∂μ)=(1:ℝ)/2 := by
    rw [integral_sub (integrable_const _) hi,mi]; simp; norm_num
  have hp (x y z t : Ω) :
      cross X (x,y)*otherClique X (y,z)*cross X (z,t)*mixed f (t,x)=
      (1-oneSet X y)*(1-oneSet X z)*(oneSet X x*(oneSet X t*mixed f (x,t))) := by
    rw [three_edge_product]
    dsimp [mixed]
    ring
  have hgg : (∫ a, ∫ b, (1-oneSet X a)*(1-oneSet X b) ∂μ ∂μ)=(1:ℝ)/4 := by
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
    simp only [mg]
    norm_num
  unfold cycle4
  simp_rw [hp,integral_const_mul]
  simp_rw [integral_mul_const]
  rw [hgg,integral_const_mul]
  have hsame : (∫ x, oneSet X x*(∫ t, oneSet X t*mixed f (x,t) ∂μ) ∂μ)=
      ∫ x in X, ∫ t in X, f x*(1-f t)+(1-f x)*f t ∂μ ∂μ := by
    have hinner (x : Ω) : (∫ t, oneSet X t*mixed f (x,t) ∂μ)=∫ t in X, mixed f (x,t) ∂μ := by
      rw [← ThirdsMixingAnchor.integral_mul_indicator μ (fun t => mixed f (x,t)) X hX]
      congr 1; funext t; ring
    simp_rw [hinner]
    change (∫ x, oneSet X x*(∫ t in X, mixed f (x,t) ∂μ) ∂μ)=
      ∫ x in X, ∫ t in X, mixed f (x,t) ∂μ ∂μ
    rw [← ThirdsMixingAnchor.integral_mul_indicator μ (fun x => ∫ t in X, mixed f (x,t) ∂μ) X hX]
    congr 1; funext x; ring
  rw [← hsame]
lemma zero_forces_binary (X : Set Ω) (hX : MeasurableSet X) (mX : μ.real X=(1:ℝ)/2)
    (f : Ω → ℝ) (hf : Measurable f) (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (mf : ∫ x, f x ∂μ=(1:ℝ)/2)
    (hz : cycle4 μ (cross X) (otherClique X) (cross X) (mixed f)=0) :
    (f =ᵐ[μ] oneSet X) ∨ (f =ᵐ[μ] (fun x => 1-oneSet X x)) := by
  by_contra hn
  have hp := ThirdsMixingAnchor.mixing_positive μ f hf bf mf X hX mX hn
  rw [cross_clique_cycle μ X hX mX f hf bf] at hz
  nlinarith
end ThirdsCrossClique
end JigBundleModule84

/- Inlined module ThirdsForcedHalfRow; original SHA256 14bf42678cd3a270acfe14ce335953e277c42c38f382aa4374fb31a7a8f24666 -/
section JigBundleModule85
open MeasureTheory
namespace ThirdsForcedHalfRow
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma zero_half_row (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (mf : ∫ x, f x ∂μ=(1:ℝ)/2)
    (X : Set Ω) (hX : MeasurableSet X) (mX : μ.real X=(1:ℝ)/2)
    (hz : ∫ x in X, f x ∂μ=0) :
    f =ᵐ[μ] (fun x => 1-oneSet X x) := by
  rcases ThirdsMixingAnchor.endpoint_alignment μ f hf bf mf X hX mX (Or.inl hz) with hh|hh
  · have hi : (∫ x in X, f x ∂μ)=μ.real X := by
      rw [integral_congr_ae (ae_restrict_of_ae hh)]
      simp [oneSet,integral_indicator hX]
    rw [hz,mX] at hi
    norm_num at hi
  · exact hh
lemma full_clique_outside_zero (C : Ω × Ω → ℝ) (X : Set Ω) (hX : MeasurableSet X)
    (hs : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (hc : ∀ᵐ p ∂μ.prod μ, p.1∈X → C p=oneSet X p.2) :
    ∀ᵐ u ∂μ, u∉X → (∫ x in X, C (u,x) ∂μ)=0 := by
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  have hp : ∀ᵐ p ∂μ.prod μ, p.1∉X → p.2∈X → C p=0 := by
    filter_upwards [hs,hswap] with p sp cp
    intro hp1 hp2
    change p.2∈X → C (p.2,p.1)=oneSet X p.1 at cp
    rw [sp,cp hp2]
    simp [oneSet,hp1]
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with u hu
  intro hun
  have hz : (fun x => C (u,x)) =ᵐ[μ.restrict X] (fun _ => 0) := by
    apply (ae_restrict_iff' hX).mpr
    filter_upwards [hu] with x hx
    intro hxx
    exact hx hun hxx
  rw [integral_congr_ae hz,integral_zero]
end ThirdsForcedHalfRow
end JigBundleModule85

/- Inlined module ThirdsTransportSupport; original SHA256 75088ee9406b1f4b4c8c7fb1f932a207b80ed591285c5067e4f18791fe0626c9 -/
section JigBundleModule86
open MeasureTheory
namespace ThirdsTransportSupport
open TwoPairHalfSetOperator ThirdsDeterministicTransport
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma given_support (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p≤1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (d : ℝ) (hd : d≠0) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (S T : Set Ω) (hS : MeasurableSet S)
    (hf : act μ C (oneSet S) =ᵐ[μ] (fun x => d*oneSet T x)) :
    ∀ᵐ p ∂μ.prod μ, 0<C p → oneSet T p.1=oneSet S p.2 := by
  have he : ∀ᵐ x ∂μ, act μ C (oneSet S) x=0 ∨ act μ C (oneSet S) x=d := by
    filter_upwards [hf] with x hx
    rcases oneSet_binary T x with ht|ht
    · left; simpa [ht] using hx
    · right; simpa [ht] using hx
  obtain ⟨U,hU,mU,hu,hc⟩ := deterministic_transport μ C hC bC sC d hd hr S hS he
  have ht : oneSet T =ᵐ[μ] oneSet U := by
    filter_upwards [hf,hu] with x hx hux
    exact mul_left_cancel₀ hd (hx.symm.trans hux)
  have hl := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae ht
  filter_upwards [hc,hl] with p hp hlp
  intro hpos
  exact hlp.trans (hp hpos)
lemma outside_zero (C : Ω × Ω → ℝ)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p)
    (S T : Set Ω)
    (hc : ∀ᵐ p ∂μ.prod μ, 0<C p → oneSet T p.1=oneSet S p.2) :
    ∀ᵐ p ∂μ.prod μ, p.1∈T → p.2∉S → C p=0 := by
  filter_upwards [bC,hc] with p hp hh
  intro ht hs
  apply le_antisymm _ hp
  apply le_of_not_gt
  intro hpos
  have he := hh hpos
  simp [oneSet,ht,hs] at he
end ThirdsTransportSupport
end JigBundleModule86

/- Inlined module ThirdsCaseACut; original SHA256 daca8fba5098e00124a9adbb640770815d83565dcc7bbb7ee6d05d580fddc486 -/
section JigBundleModule87
open MeasureTheory
namespace ThirdsCaseACut
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma case_a_cut (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0 < d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d)
    (hi0 : ∀ᵐ x ∂μ, x∈S → act μ (W 0) (oneSet S) x=d)
    (hi1 : ∀ᵐ x ∂μ, x∈S → act μ (W 1) (oneSet S) x=d)
    (hCD : ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W 0 p+W 1 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0) :
    ∃ X : Set Ω, ∃ e : ℝ, ∃ r : Ω → ℝ,
      MeasurableSet X ∧ μ.real (X∩S)=d ∧ (e=1 ∨ e= -1) ∧
      Measurable r ∧ (∀ x, -1 ≤ r x ∧ r x ≤ 1) ∧
      (r =ᵐ[ProbabilityTheory.cond μ S] (fun x => 2*oneSet X x-1)) ∧
      (W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)]
        (fun p => (1+e*r p.1*r p.2)/2)) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd hmS
  have ha : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hap := ha.prod ha
  obtain ⟨T,hT,mT,hf,σ,u,v,hσ0,hσ1,hu,hv,_,_,huR,hvR,huact,hvact,hz1,hz2⟩ :=
    ThirdsCaseAAnchors.case_a_anchors μ W hW bW sW hpart d hd hr S hS hmS hend hi0 hi1 hz
      (RowGood μ W) (rowGood_ae μ W bW sW hpart)
  have mui (c : Fin 6) (hc : u∈T c) : act μ (W c) (oneSet S) u=d := by
    rw [huact c]; simp [oneSet,hc]
  have mvi (c : Fin 6) (hc : v∈T c) : act μ (W c) (oneSet S) v=d := by
    rw [hvact c]; simp [oneSet,hc]
  obtain ⟨r,hrr,br,mr,_,_,er⟩ := selected_center μ W hW S hS d hd hmS u huR
    (σ 2) (σ 3) (σ.injective.ne (by decide)) (mui _ hu.1) (mui _ hu.2)
  obtain ⟨s,hss,bs,ms,_,_,es⟩ := selected_center μ W hW S hS d hd hmS v hvR
    (σ 4) (σ 5) (σ.injective.ne (by decide)) (mvi _ hv.1) (mvi _ hv.2)
  have hsum : ∀ᵐ p ∂ν.prod ν, W 0 p+W 1 p=1 := by
    have hsν : ∀ᵐ x ∂ν, x∈S := ThirdsNormalizedRestriction.conditional_ae μ S hS _
      (Filter.Eventually.of_forall (fun _ hx => hx))
    have hxy : ∀ᵐ p ∂ν.prod ν, p.1∈S ∧ p.2∈S := by
      apply (Measure.ae_prod_iff_ae_ae (hS.prod hS)).mpr
      filter_upwards [hsν] with x hx
      filter_upwards [hsν] with y hy
      exact ⟨hx,hy⟩
    filter_upwards [hCD.filter_mono hap.ae_le,hxy] with p hp hxy
    exact hp hxy.1 hxy.2
  have hrow : ∀ᵐ x ∂ν, ∫ y, W 0 (x,y) ∂ν=(1:ℝ)/2 := by
    apply ThirdsNormalizedRestriction.conditional_row_half μ S hS d hd hmS
    filter_upwards [hi0] with x hx
    simpa only [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ (W 0) S hS] using hx
  have z1 : cycle4 ν (W 0) (W 1) (anchor s) (anchor r)=0 := by
    have zz : cycle4 ν (W 0) (W 1) (ThirdsCanonicalAnchors.bridge W (σ 4) (σ 5) v)
      (ThirdsCanonicalAnchors.bridge W (σ 2) (σ 3) u)=0 := by
        change cycle4 ν (W (σ 0)) (W (σ 1)) (ThirdsCanonicalAnchors.bridge W (σ 4) (σ 5) v)
          (ThirdsCanonicalAnchors.bridge W (σ 2) (σ 3) u)=0 at hz1
        simpa only [hσ0,hσ1] using hz1
    rw [← cycle4_congr ν Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl es er]
    exact zz
  have z2 : cycle4 ν (W 0) (anchor r) (W 1) (anchor s)=0 := by
    have zz : cycle4 ν (W 0) (ThirdsCanonicalAnchors.bridge W (σ 2) (σ 3) u)
      (W 1) (ThirdsCanonicalAnchors.bridge W (σ 4) (σ 5) v)=0 := by
        change cycle4 ν (W (σ 0)) (ThirdsCanonicalAnchors.bridge W (σ 2) (σ 3) u)
          (W (σ 1)) (ThirdsCanonicalAnchors.bridge W (σ 4) (σ 5) v)=0 at hz2
        simpa only [hσ0,hσ1] using hz2
    rw [← cycle4_congr ν Filter.EventuallyEq.rfl er Filter.EventuallyEq.rfl es]
    exact zz
  obtain ⟨X,e,hX,mX,he,hrX,_,hkernel⟩ := ThirdsAENormalizedAnchor.normalized_anchor_ae ν
    (W 0) (W 1) r s (hW 0) (hW 1) hrr hss ((bW 0).filter_mono hap.ae_le)
    ((sW 0).filter_mono hap.ae_le) hsum br bs hrow mr ms z1 z2
  exact ⟨X,e,r,hX,ThirdsNormalizedRestriction.ambient_half_mass μ S X hX d hd hmS mX,
    he,hrr,br,hrX,hkernel⟩
end ThirdsCaseACut
end JigBundleModule87

/- Inlined module ThirdsAnchorPropagation; original SHA256 614b68c14c24aba1ccb401faa87fb36a35b07eb40855bf3d3d69fcef580ce1f9 -/
section JigBundleModule88
open MeasureTheory
namespace ThirdsAnchorPropagation
open TwoPairHalfSetOperator ThirdsRankOneComp
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma propagate (C D : Ω × Ω → ℝ) (r s t : Ω → ℝ) (e : ℝ)
    (hC : Measurable C) (hD : Measurable D) (hs : Measurable s) (ht : Measurable t)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (hCD : ∀ᵐ p ∂μ.prod μ, C p+D p=1)
    (bs : ∀ x, -1 ≤ s x ∧ s x ≤ 1) (bt : ∀ x, -1 ≤ t x ∧ t x ≤ 1)
    (hrow : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=(1:ℝ)/2)
    (ms : ∫ x, s x ∂μ=0) (mt : ∫ x, t x ∂μ=0)
    (he : e=1 ∨ e= -1) (br : ∀ᵐ x ∂μ, r x=1 ∨ r x= -1)
    (hCr : C =ᵐ[μ.prod μ] (fun p => (1+e*r p.1*r p.2)/2))
    (hz1 : cycle4 μ C D (anchor t) (anchor s)=0)
    (hz2 : cycle4 μ C (anchor s) D (anchor t)=0) :
    ((s =ᵐ[μ] r) ∨ (s =ᵐ[μ] (fun x => -r x))) ∧
    ((t =ᵐ[μ] r) ∨ (t =ᵐ[μ] (fun x => -r x))) := by
  obtain ⟨X,f,_,_,hf,hsX,hst,hCs⟩ := ThirdsAENormalizedAnchor.normalized_anchor_ae μ C D s t
    hC hD hs ht bC sC hCD bs bt hrow ms mt hz1 hz2
  have sb : ∀ᵐ x ∂μ, s x=1 ∨ s x= -1 := by
    filter_upwards [hsX] with x hx
    have hh := oneSet_binary X x
    rcases hh with hh|hh
    · right; simpa only [hh,mul_zero,zero_sub] using hx
    · left; norm_num [hh] at hx ⊢; exact hx
  have hsr := ThirdsRankOneUnique.unique_anchor μ C s r f e hf he sb br hCs hCr
  refine ⟨hsr,?_⟩
  rcases hst with hst|hst <;> rcases hsr with hsr|hsr
  · left; exact hst.symm.trans hsr
  · right; exact hst.symm.trans hsr
  · right
    filter_upwards [hst,hsr] with x h1 h2
    change s x= -t x at h1
    change s x=r x at h2
    change t x= -r x
    linarith
  · left
    filter_upwards [hst,hsr] with x h1 h2
    change s x= -t x at h1
    change s x= -r x at h2
    change t x=r x
    linarith
end ThirdsAnchorPropagation
end JigBundleModule88

/- Inlined module ThirdsPairRowAlignment; original SHA256 295971f529712558360bf5029e9fdd7a82edb68cb2faa4d563306722fff65461 -/
section JigBundleModule89
open MeasureTheory
namespace ThirdsPairRowAlignment
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma pair_rows_align (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hf : ∀ i, act μ (W i) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T i) x))
    (hp : μ (T 4∩T 5) ≠ 0)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hCD : ∀ᵐ p ∂(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S), W 0 p+W 1 p=1)
    (hrow : ∀ᵐ x ∂ProbabilityTheory.cond μ S, ∫ y, W 0 (x,y) ∂ProbabilityTheory.cond μ S=(1:ℝ)/2)
    (r : Ω → ℝ) (e : ℝ) (he : e=1 ∨ e= -1)
    (br : ∀ᵐ x ∂ProbabilityTheory.cond μ S, r x=1 ∨ r x= -1)
    (hCr : W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)]
      (fun p => (1+e*r p.1*r p.2)/2)) :
    ∀ᵐ u ∂μ, u∈T 2∩T 3 →
      (((fun x => W 2 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2)) ∧
       ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2))) ∨
      (((fun x => W 2 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2)) ∧
       ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2))) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd mS
  have ha : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hap := ha.prod ha
  have hnS : μ S ≠ 0 := by
    intro h
    have hh : μ.real S=0 := by simp [measureReal_def,h]
    linarith
  have hzuv := ThirdsAEAnchors.canonical_anchor_zeros μ W hW bW sW hz S hS hnS
  have hRG := rowGood_ae μ W bW sW hpart
  have hact := ae_all_iff.mpr hf
  filter_upwards [hzuv,hRG,hact] with u hzu hgu hau
  intro hu
  have hvg : ∀ᵐ v ∂μ, RowGood μ W v ∧
      (∀ c, act μ (W c) (oneSet S) v=d*oneSet (T c) v) ∧
      cycle4 ν (W 0) (W 1) (ThirdsCanonicalAnchors.bridge W 4 5 v) (ThirdsCanonicalAnchors.bridge W 2 3 u)=0 ∧
      cycle4 ν (W 0) (ThirdsCanonicalAnchors.bridge W 2 3 u) (W 1) (ThirdsCanonicalAnchors.bridge W 4 5 v)=0 := by
    filter_upwards [hRG,hact,hzu] with v hgv hav hzv
    exact ⟨hgv,hav,hzv.1,hzv.2⟩
  obtain ⟨v,hv,hgv,hav,hz1,hz2⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp (ae_restrict_of_ae hvg)
  have mui (c : Fin 6) (hc : u∈T c) : act μ (W c) (oneSet S) u=d := by
    rw [hau c]; simp [oneSet,hc]
  have mvi (c : Fin 6) (hc : v∈T c) : act μ (W c) (oneSet S) v=d := by
    rw [hav c]; simp [oneSet,hc]
  obtain ⟨s,hs,bs,ms,esi,esj,es⟩ := selected_center μ W hW S hS d hd mS u hgu 2 3
    (by decide) (mui _ hu.1) (mui _ hu.2)
  obtain ⟨t,ht,bt,mt,_,_,et⟩ := selected_center μ W hW S hS d hd mS v hgv 4 5
    (by decide) (mvi _ hv.1) (mvi _ hv.2)
  have z1 : cycle4 ν (W 0) (W 1) (anchor t) (anchor s)=0 := by
    rw [← cycle4_congr ν Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl et es]
    exact hz1
  have z2 : cycle4 ν (W 0) (anchor s) (W 1) (anchor t)=0 := by
    rw [← cycle4_congr ν Filter.EventuallyEq.rfl es Filter.EventuallyEq.rfl et]
    exact hz2
  have hal := (ThirdsAnchorPropagation.propagate ν (W 0) (W 1) r s t e (hW 0) (hW 1) hs ht
    ((bW 0).filter_mono hap.ae_le) ((sW 0).filter_mono hap.ae_le) hCD bs bt hrow ms mt he br hCr z1 z2).1
  rcases hal with hal|hal
  · left
    constructor
    · filter_upwards [esi,hal] with x hx hh; simpa only [hh] using hx
    · filter_upwards [esj,hal] with x hx hh; simpa only [hh] using hx
  · right
    constructor
    · filter_upwards [esi,hal] with x hx hh
      change s x= -r x at hh
      change W 2 (u,x)=(1-r x)/2
      change W 2 (u,x)=(1+s x)/2 at hx
      rw [hh] at hx; linarith
    · filter_upwards [esj,hal] with x hx hh
      change s x= -r x at hh
      change W 3 (u,x)=(1+r x)/2
      change W 3 (u,x)=(1-s x)/2 at hx
      rw [hh] at hx; linarith
end ThirdsPairRowAlignment
end JigBundleModule89

/- Inlined module ThirdsComplementaryMass; original SHA256 1a2c2a9e1bea5f9157b4bfb9b9cd21b952f1df06ef5e7bc1a07c61077bd09f9d -/
section JigBundleModule90
open MeasureTheory
namespace ThirdsComplementaryMass
open TwoPairHalfSetOperator ThirdsPairMass
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma complementary_masses (T : Fin 4 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (d : ℝ) (hm : ∀ i, μ.real (T i)=2*d)
    (hc : ∀ᵐ x ∂μ, (∑ i, oneSet (T i) x)=0 ∨ (∑ i, oneSet (T i) x)=2) :
    μ.real (T 0∩T 1)=μ.real (T 2∩T 3) ∧
    μ.real (T 0∩T 2)=μ.real (T 1∩T 3) ∧
    μ.real (T 0∩T 3)=μ.real (T 1∩T 2) := by
  have hc' : ∀ᵐ x ∂μ, oneSet (T 0) x+oneSet (T 1) x+oneSet (T 2) x+oneSet (T 3) x=0 ∨
      oneSet (T 0) x+oneSet (T 1) x+oneSet (T 2) x+oneSet (T 3) x=2 := by
    simpa only [Fin.sum_univ_four] using hc
  have h0 := degree_mass μ (T 0) (T 1) (T 2) (T 3) (hT 0) (hT 1) (hT 2) (hT 3) (by
    filter_upwards [hc'] with x hx
    exact binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) hx)
  have h1 := degree_mass μ (T 1) (T 0) (T 2) (T 3) (hT 1) (hT 0) (hT 2) (hT 3) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _)
    rcases hx with hx|hx
    · left; linarith
    · right; linarith)
  have h2 := degree_mass μ (T 2) (T 0) (T 1) (T 3) (hT 2) (hT 0) (hT 1) (hT 3) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _)
    rcases hx with hx|hx
    · left; linarith
    · right; linarith)
  have h3 := degree_mass μ (T 3) (T 0) (T 1) (T 2) (hT 3) (hT 0) (hT 1) (hT 2) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _) (oneSet_binary _ _)
    rcases hx with hx|hx
    · left; linarith
    · right; linarith)
  rw [hm 0] at h0
  rw [hm 1,Set.inter_comm (T 1) (T 0)] at h1
  rw [hm 2,Set.inter_comm (T 2) (T 0),Set.inter_comm (T 2) (T 1)] at h2
  rw [hm 3,Set.inter_comm (T 3) (T 0),Set.inter_comm (T 3) (T 1),Set.inter_comm (T 3) (T 2)] at h3
  have he0 : μ.real (T 0∩T 1)=μ.real (T 2∩T 3) := by linarith
  have he1 : μ.real (T 0∩T 2)=μ.real (T 1∩T 3) := by linarith
  have he2 : μ.real (T 0∩T 3)=μ.real (T 1∩T 2) := by linarith
  exact ⟨he0,he1,he2⟩
end ThirdsComplementaryMass
end JigBundleModule90

/- Inlined module ThirdsAllPairAlignment; original SHA256 cdf29bcf0b68d5235217fbac174abaa70428b537e6ba9db8f78937a1daa29f99 -/
section JigBundleModule91
open MeasureTheory
namespace ThirdsAllPairAlignment
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma pair_rows_align_without_positivity (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hf : ∀ i, act μ (W i) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T i) x))
    (hcomp : μ.real (T 2∩T 3)=μ.real (T 4∩T 5))
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hCD : ∀ᵐ p ∂(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S), W 0 p+W 1 p=1)
    (hrow : ∀ᵐ x ∂ProbabilityTheory.cond μ S, ∫ y, W 0 (x,y) ∂ProbabilityTheory.cond μ S=(1:ℝ)/2)
    (r : Ω → ℝ) (e : ℝ) (he : e=1 ∨ e= -1)
    (br : ∀ᵐ x ∂ProbabilityTheory.cond μ S, r x=1 ∨ r x= -1)
    (hCr : W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)]
      (fun p => (1+e*r p.1*r p.2)/2)) :
    ∀ᵐ u ∂μ, u∈T 2∩T 3 →
      (((fun x => W 2 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2)) ∧
       ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2))) ∨
      (((fun x => W 2 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2)) ∧
       ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2))) := by
  by_cases hp : μ (T 4∩T 5) ≠ 0
  · exact ThirdsPairRowAlignment.pair_rows_align μ W hW bW sW hpart S hS d hd mS T hT hf hp hz hCD hrow r e he br hCr
  · have hp0 : μ (T 4∩T 5)=0 := not_ne_iff.mp hp
    have hz0 : μ.real (T 2∩T 3)=0 := by rw [hcomp]; simp [measureReal_def,hp0]
    have hm0 : μ (T 2∩T 3)=0 := (measureReal_eq_zero_iff).mp hz0
    have hn : ∀ᵐ u ∂μ, u∉T 2∩T 3 := by
      simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hm0
    filter_upwards [hn] with u hu
    intro hx
    exact (hu hx).elim
end ThirdsAllPairAlignment
end JigBundleModule91

/- Inlined module ThirdsPermutedPairMass; original SHA256 735daa987527b37203a4f54561eb06ed178cac514f90570200b3ae370b84215e -/
section JigBundleModule92
open MeasureTheory
namespace ThirdsPermutedPairMass
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma permuted_pair_mass (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (S : Set Ω) (d : ℝ) (hm : ∀ i, μ.real (T i)=2*d)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (h1 : oneSet (T 1) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, ∑ i, oneSet (T i) x=2)
    (σ : Equiv.Perm (Fin 6)) (hσ0 : σ 0=0) (hσ1 : σ 1=1) :
    μ.real (T (σ 2)∩T (σ 3))=μ.real (T (σ 4)∩T (σ 5)) := by
  let U : Fin 4 → Set Ω := ![T (σ 2),T (σ 3),T (σ 4),T (σ 5)]
  have hu : ∀ᵐ x ∂μ, (∑ i, oneSet (U i) x)=0 ∨ (∑ i, oneSet (U i) x)=2 := by
    filter_upwards [h0,h1,hc] with x hx0 hx1 hcx
    have he : (∑ i, oneSet (T (σ i)) x)=∑ i, oneSet (T i) x := Equiv.sum_comp σ (fun i => oneSet (T i) x)
    rw [hcx] at he
    simp only [Fin.sum_univ_six,hσ0,hσ1,hx0,hx1] at he
    simp only [Fin.sum_univ_four,U,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_fin_one]
    rcases oneSet_binary S x with hx|hx
    · right; rw [hx] at he; linarith
    · left; rw [hx] at he; linarith
  have hmu : ∀ i, μ.real (U i)=2*d := by intro i; fin_cases i <;> exact hm _
  have hU : ∀ i, MeasurableSet (U i) := by intro i; fin_cases i <;> exact hT _
  exact (ThirdsComplementaryMass.complementary_masses μ U hU d hmu hu).1
end ThirdsPermutedPairMass
end JigBundleModule92

/- Inlined module ThirdsAllRowFamilies; original SHA256 b1f7f06e5e97f6c25ae3bfe550e0c8d26076000033ed57f73c2bdf4ad670b6a1 -/
section JigBundleModule93
open MeasureTheory
namespace ThirdsAllRowFamilies
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma all_pair_rows_align (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hf : ∀ i, act μ (W i) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T i) x))
    (hmT : ∀ i, μ.real (T i)=2*d)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (h1 : oneSet (T 1) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, ∑ i, oneSet (T i) x=2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hCD : ∀ᵐ p ∂(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S), W 0 p+W 1 p=1)
    (hrow : ∀ᵐ x ∂ProbabilityTheory.cond μ S, ∫ y, W 0 (x,y) ∂ProbabilityTheory.cond μ S=(1:ℝ)/2)
    (r : Ω → ℝ) (e : ℝ) (he : e=1 ∨ e= -1)
    (br : ∀ᵐ x ∂ProbabilityTheory.cond μ S, r x=1 ∨ r x= -1)
    (hCr : W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)]
      (fun p => (1+e*r p.1*r p.2)/2)) :
    ∀ σ : Equiv.Perm (Fin 6), σ 0=0 → σ 1=1 →
    ∀ᵐ u ∂μ, u∈T (σ 2)∩T (σ 3) →
      (((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2)) ∧
       ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2))) ∨
      (((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2)) ∧
       ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2))) := by
  intro σ hσ0 hσ1
  have hpartσ : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun i => W i p)]; exact hp
  have hzσ : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have hcomp := ThirdsPermutedPairMass.permuted_pair_mass μ T hT S d hmT h0 h1 hc σ hσ0 hσ1
  have hCDσ : ∀ᵐ p ∂(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S),
      W (σ 0) p+W (σ 1) p=1 := by simpa only [hσ0,hσ1] using hCD
  have hrσ : ∀ᵐ x ∂ProbabilityTheory.cond μ S,
      ∫ y, W (σ 0) (x,y) ∂ProbabilityTheory.cond μ S=(1:ℝ)/2 := by simpa only [hσ0] using hrow
  have hCrσ : W (σ 0) =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)]
      (fun p => (1+e*r p.1*r p.2)/2) := by simpa only [hσ0] using hCr
  exact ThirdsAllPairAlignment.pair_rows_align_without_positivity μ (fun c => W (σ c))
    (fun c => hW (σ c)) (fun c => bW (σ c)) (fun c => sW (σ c)) hpartσ S hS d hd mS
    (fun c => T (σ c)) (fun c => hT (σ c)) (fun c => hf (σ c)) hcomp hzσ hCDσ hrσ r e he br hCrσ
end ThirdsAllRowFamilies
end JigBundleModule93

/- Inlined module ThirdsCaseAFamilies; original SHA256 75da0d84c189a0cc7019e8e75aa4b591238e2ef1962770379ce11dd7e6de18c6 -/
section JigBundleModule94
open MeasureTheory
namespace ThirdsCaseAFamilies
open FourColorKernels TwoPairHalfSetOperator ThirdsRankOneComp ThirdsSelectedCenter
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma case_a_families (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0 < d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d)
    (hi0 : ∀ᵐ x ∂μ, x∈S → act μ (W 0) (oneSet S) x=d)
    (hi1 : ∀ᵐ x ∂μ, x∈S → act μ (W 1) (oneSet S) x=d)
    (hCD : ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W 0 p+W 1 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0) :
    ∃ X : Set Ω, ∃ e : ℝ, ∃ r : Ω → ℝ,
      MeasurableSet X ∧ μ.real (X∩S)=d ∧ (e=1 ∨ e= -1) ∧
      Measurable r ∧ (∀ x, -1 ≤ r x ∧ r x ≤ 1) ∧
      (r =ᵐ[ProbabilityTheory.cond μ S] (fun x => 2*oneSet X x-1)) ∧
      (W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)]
        (fun p => (1+e*r p.1*r p.2)/2)) ∧
      ∃ T : Fin 6 → Set Ω, (∀ i, MeasurableSet (T i)) ∧ (∀ i, μ.real (T i)=2*d) ∧
      (∀ i, act μ (W i) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T i) x)) ∧
    ∀ σ : Equiv.Perm (Fin 6), σ 0=0 → σ 1=1 →
    ∀ᵐ u ∂μ, u∈T (σ 2)∩T (σ 3) →
      (((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2)) ∧
       ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2))) ∨
      (((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2)) ∧
       ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2))) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd hmS
  have ha : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hap := ha.prod ha
  obtain ⟨X,e,r,hX,mX,he,hrm,br,hrX,hCr⟩ := ThirdsCaseACut.case_a_cut μ W hW bW sW hpart d hd hr S hS hmS hend hi0 hi1 hCD hz
  obtain ⟨T,hT,mT,hf,_⟩ := ThirdsCaseAPairs.case_a_transport_pairs μ W hW bW sW hpart d hd hr S hS hmS hend hi0 hi1
  have he0 := ThirdsCaseAPairs.full_internal_transport μ (W 0) S (T 0) hS (hT 0)
    ((mT 0).trans hmS.symm) d hd (hf 0) hi0
  have he1 := ThirdsCaseAPairs.full_internal_transport μ (W 1) S (T 1) hS (hT 1)
    ((mT 1).trans hmS.symm) d hd (hf 1) hi1
  have hcount := ThirdsInternalCount.internal_count μ W hW bW hpart S hS d (ne_of_gt hd) hmS T hf
  have hsum : ∀ᵐ p ∂ν.prod ν, W 0 p+W 1 p=1 := by
    have hsν : ∀ᵐ x ∂ν, x∈S := ThirdsNormalizedRestriction.conditional_ae μ S hS _
      (Filter.Eventually.of_forall (fun _ hx => hx))
    have hxy : ∀ᵐ p ∂ν.prod ν, p.1∈S ∧ p.2∈S := by
      apply (Measure.ae_prod_iff_ae_ae (hS.prod hS)).mpr
      filter_upwards [hsν] with x hx
      filter_upwards [hsν] with y hy
      exact ⟨hx,hy⟩
    filter_upwards [hCD.filter_mono hap.ae_le,hxy] with p hp hxy
    exact hp hxy.1 hxy.2
  have hrow : ∀ᵐ x ∂ν, ∫ y, W 0 (x,y) ∂ν=(1:ℝ)/2 := by
    apply ThirdsNormalizedRestriction.conditional_row_half μ S hS d hd hmS
    filter_upwards [hi0] with x hx
    simpa only [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ (W 0) S hS] using hx
  have hrb : ∀ᵐ x ∂ν, r x=1 ∨ r x= -1 := by
    filter_upwards [hrX] with x hx
    rcases oneSet_binary X x with hh|hh
    · right; simpa only [hh,mul_zero,zero_sub] using hx
    · left; norm_num [hh] at hx ⊢; exact hx
  refine ⟨X,e,r,hX,mX,he,hrm,br,hrX,hCr,T,hT,mT,hf,?_⟩
  exact ThirdsAllRowFamilies.all_pair_rows_align μ W hW bW sW hpart S hS d hd hmS T hT hf
    mT he0 he1 hcount hz hsum hrow r e he hrb hCr
end ThirdsCaseAFamilies
end JigBundleModule94

/- Inlined module ThirdsOutsidePairLabels; original SHA256 56eb600403a25c47e0cecc753b2b95dab482ad1a15da5ad9a5ac9b505a01bd21 -/
section JigBundleModule95
open MeasureTheory
namespace ThirdsOutsidePairLabels
lemma pair_permutation (i j : Fin 6) (hi0 : i≠0) (hi1 : i≠1) (hj0 : j≠0) (hj1 : j≠1) (hij : i≠j) :
    ∃ σ : Equiv.Perm (Fin 6), σ 0=0 ∧ σ 1=1 ∧ σ 2=i ∧ σ 3=j := by
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals first
    | exact ⟨Equiv.ofBijective ![0,1,2,3,4,5] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,2,4,3,5] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,2,5,3,4] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,3,2,4,5] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,3,4,2,5] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,3,5,2,4] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,4,2,3,5] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,4,3,2,5] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,4,5,2,3] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,5,2,3,4] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,5,3,2,4] (by decide),rfl,rfl,rfl,rfl⟩
    | exact ⟨Equiv.ofBijective ![0,1,5,4,2,3] (by decide),rfl,rfl,rfl,rfl⟩
lemma active_partner (t : Fin 6 → ℝ) (hb : ∀ i, t i=0 ∨ t i=1)
    (hs : ∑ i, t i=2) (h0 : t 0=0) (h1 : t 1=0) (i : Fin 6) (hi : t i=1) :
    ∃ j : Fin 6, i≠0 ∧ i≠1 ∧ j≠0 ∧ j≠1 ∧ i≠j ∧ t j=1 := by
  classical
  have hi0 : i≠0 := by intro h; subst i; linarith
  have hi1 : i≠1 := by intro h; subst i; linarith
  have hj : ∃ j, j≠i ∧ t j=1 := by
    by_contra h
    push_neg at h
    have ht : ∀ j, j≠i → t j=0 := by
      intro j hji
      rcases hb j with hj|hj
      · exact hj
      · exact (h j hji hj).elim
    have he : (∑ j, t j)=t i := Finset.sum_eq_single i
      (fun j _ hji => ht j hji) (fun h => (h (Finset.mem_univ i)).elim)
    linarith
  obtain ⟨j,hji,hj⟩ := hj
  have hj0 : j≠0 := by intro h; subst j; linarith
  have hj1 : j≠1 := by intro h; subst j; linarith
  exact ⟨j,hi0,hi1,hj0,hj1,Ne.symm hji,hj⟩
end ThirdsOutsidePairLabels
end JigBundleModule95

/- Inlined module ThirdsOutsideProfiles; original SHA256 81de1537134c50459a360c44ad2e97f0c5c8fc235a05dd1f08d4cbff07e30756 -/
section JigBundleModule96
open MeasureTheory
namespace ThirdsOutsideProfiles
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
def Profile (ν : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (r : Ω → ℝ) (c : Fin 6) (u : Ω) : Prop :=
  ((fun x => W c (u,x)) =ᵐ[ν] (fun _ => 0)) ∨
  ((fun x => W c (u,x)) =ᵐ[ν] (fun x => (1+r x)/2)) ∨
  ((fun x => W c (u,x)) =ᵐ[ν] (fun x => (1-r x)/2))
lemma inactive_zero (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d)
    (u : Ω) (hu : RowGood μ W u) (c : Fin 6) (hz : act μ (W c) (oneSet S) u=0) :
    (fun x => W c (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun _ => 0) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd mS
  have ha : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have bb : ∀ᵐ x ∂ν, 0 ≤ W c (u,x) ∧ W c (u,x) ≤ 1 :=
    ((hu.1 c).filter_mono ha.ae_le).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have hi := LowSupportAnalysis.unit_integrable_ae
    ((hW c).comp (measurable_const.prodMk measurable_id)) bb
  have hzν : (∫ x, W c (u,x) ∂ν)=0 := by
    rw [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ (W c) S hS] at hz
    rw [ThirdsNormalizedRestriction.conditional_integral μ S,hz,mul_zero]
  exact (integral_eq_zero_iff_of_nonneg_ae (bb.mono fun _ h => h.1) hi).mp hzν
lemma outside_rows (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (S : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (r : Ω → ℝ)
    (hRG : ∀ᵐ u ∂μ, RowGood μ W u)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (h1 : oneSet (T 1) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hall : ∀ σ : Equiv.Perm (Fin 6), σ 0=0 → σ 1=1 →
      ∀ᵐ u ∂μ, u∈T (σ 2)∩T (σ 3) →
        ((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2)) ∨
        ((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2))) :
    ∀ᵐ u ∂μ, u∉S → ∀ c, Profile (ProbabilityTheory.cond μ S) W r c u := by
  have ha : ∀ σ : Equiv.Perm (Fin 6), ∀ᵐ u ∂μ, σ 0=0 → σ 1=1 → u∈T (σ 2)∩T (σ 3) →
        ((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1+r x)/2)) ∨
        ((fun x => W (σ 2) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => (1-r x)/2)) := by
    intro σ
    by_cases hσ0 : σ 0=0
    · by_cases hσ1 : σ 1=1
      · filter_upwards [hall σ hσ0 hσ1] with u hu; exact fun _ _ => hu
      · exact Filter.Eventually.of_forall (fun _ _ h => (hσ1 h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (hσ0 h).elim)
  filter_upwards [hRG,ae_all_iff.mpr hf,h0,h1,hc,ae_all_iff.mpr ha] with u hgu hfu hu0 hu1 hcu hau
  intro hus c
  by_cases hct : u∈T c
  · have hi : oneSet (T c) u=1 := by simp [oneSet,hct]
    have ht0 : oneSet (T 0) u=0 := by rw [hu0]; simp [oneSet,hus]
    have ht1 : oneSet (T 1) u=0 := by rw [hu1]; simp [oneSet,hus]
    obtain ⟨j,hc0,hc1,hj0,hj1,hcj,hj⟩ := ThirdsOutsidePairLabels.active_partner
      (fun i => oneSet (T i) u) (fun i => oneSet_binary (T i) u) hcu ht0 ht1 c hi
    have hjt : u∈T j := by by_contra h; simp [oneSet,h] at hj
    obtain ⟨σ,hσ0,hσ1,hσ2,hσ3⟩ := ThirdsOutsidePairLabels.pair_permutation c j hc0 hc1 hj0 hj1 hcj
    have hh := hau σ hσ0 hσ1 (show u∈T (σ 2)∩T (σ 3) by rw [hσ2,hσ3]; exact ⟨hct,hjt⟩)
    right
    simpa only [hσ2] using hh
  · left
    apply inactive_zero μ W hW S hS d hd mS u hgu c
    rw [hfu c]; simp [oneSet,hct]
end ThirdsOutsideProfiles
end JigBundleModule96

/- Inlined module ThirdsInternalProfiles; original SHA256 9853a5ed4cb35115d275da40abd81e9160b06efe20b6249d513f4df0789be300 -/
section JigBundleModule97
open MeasureTheory
namespace ThirdsInternalProfiles
open ThirdsOutsideProfiles
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma conditional_ae_iff (S : Set Ω) (hS : MeasurableSet S) (P : Ω → Prop) :
    (∀ᵐ x ∂ProbabilityTheory.cond μ S, P x) ↔ (∀ᵐ x ∂μ, x∈S → P x) := by
  unfold ProbabilityTheory.cond
  rw [Measure.ae_ennreal_smul_measure_iff (by simp)]
  exact ae_restrict_iff' hS
lemma internal_rows (W : Fin 6 → Ω × Ω → ℝ) (r : Ω → ℝ) (e : ℝ)
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p)
    (hp : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (hs : ∀ᵐ p ∂μ.prod μ, W 0 p+W 1 p=1)
    (he : e=1 ∨ e= -1) (hr : ∀ᵐ x ∂μ, r x=1 ∨ r x= -1)
    (hk : W 0 =ᵐ[μ.prod μ] (fun p => (1+e*r p.1*r p.2)/2)) :
    ∀ᵐ u ∂μ, ∀ c, Profile μ W r c u := by
  have hz : ∀ᵐ p ∂μ.prod μ, ∀ c : Fin 6, c≠0 → c≠1 → W c p=0 := by
    filter_upwards [ae_all_iff.mpr hb,hp,hs] with p bp pp sp
    simp only [Fin.sum_univ_six] at pp
    intro c hc0 hc1
    fin_cases c <;> simp_all <;> nlinarith [bp 2,bp 3,bp 4,bp 5]
  filter_upwards [Measure.ae_ae_of_ae_prod hz,Measure.ae_ae_of_ae_prod hs,
    Measure.ae_ae_of_ae_prod hk,hr] with u hzu hsu hku hru
  intro c
  by_cases hc0 : c=0
  · subst c
    right
    rcases he with he|he <;> rcases hru with hru|hru
    · left; filter_upwards [hku] with y hy; simpa [he,hru] using hy
    · right; filter_upwards [hku] with y hy; change W 0 (u,y)=(1-r y)/2; change W 0 (u,y)=(1+e*r u*r y)/2 at hy; rw [he,hru] at hy; nlinarith
    · right; filter_upwards [hku] with y hy; change W 0 (u,y)=(1-r y)/2; change W 0 (u,y)=(1+e*r u*r y)/2 at hy; rw [he,hru] at hy; nlinarith
    · left; filter_upwards [hku] with y hy; change W 0 (u,y)=(1+r y)/2; change W 0 (u,y)=(1+e*r u*r y)/2 at hy; rw [he,hru] at hy; nlinarith
  by_cases hc1 : c=1
  · subst c
    right
    rcases he with he|he <;> rcases hru with hru|hru
    · right; filter_upwards [hku,hsu] with y hy hy'; change W 0 (u,y)=(1+e*r u*r y)/2 at hy; change W 1 (u,y)=(1-r y)/2; rw [he,hru] at hy; nlinarith
    · left; filter_upwards [hku,hsu] with y hy hy'; change W 0 (u,y)=(1+e*r u*r y)/2 at hy; change W 1 (u,y)=(1+r y)/2; rw [he,hru] at hy; nlinarith
    · left; filter_upwards [hku,hsu] with y hy hy'; change W 0 (u,y)=(1+e*r u*r y)/2 at hy; change W 1 (u,y)=(1+r y)/2; rw [he,hru] at hy; nlinarith
    · right; filter_upwards [hku,hsu] with y hy hy'; change W 0 (u,y)=(1+e*r u*r y)/2 at hy; change W 1 (u,y)=(1-r y)/2; rw [he,hru] at hy; nlinarith
  · left
    filter_upwards [hzu] with y hy
    exact hy c hc0 hc1
end ThirdsInternalProfiles
end JigBundleModule97

/- Inlined module ThirdsCaseAProfiles; original SHA256 842747dee83204669bbb3ef01335d7c47b9d44899eff8384720943e806829909 -/
section JigBundleModule98
open MeasureTheory
namespace ThirdsCaseAProfiles
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter ThirdsOutsideProfiles
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma case_a_profiles (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0 < d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d)
    (hi0 : ∀ᵐ x ∂μ, x∈S → act μ (W 0) (oneSet S) x=d)
    (hi1 : ∀ᵐ x ∂μ, x∈S → act μ (W 1) (oneSet S) x=d)
    (hCD : ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W 0 p+W 1 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0) :
    ∃ X : Set Ω, ∃ r : Ω → ℝ, MeasurableSet X ∧ μ.real (X∩S)=d ∧ Measurable r ∧
      (r =ᵐ[ProbabilityTheory.cond μ S] (fun x => 2*oneSet X x-1)) ∧
      (∀ᵐ u ∂μ, ∀ c, Profile (ProbabilityTheory.cond μ S) W r c u) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd hmS
  have ha : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hap := ha.prod ha
  obtain ⟨X,e,r,hX,mX,he,hrm,br,hrX,hCr,T,hT,mT,hf,hfamilies⟩ :=
    ThirdsCaseAFamilies.case_a_families μ W hW bW sW hpart d hd hr S hS hmS hend hi0 hi1 hCD hz
  have he0 := ThirdsCaseAPairs.full_internal_transport μ (W 0) S (T 0) hS (hT 0)
    ((mT 0).trans hmS.symm) d hd (hf 0) hi0
  have he1 := ThirdsCaseAPairs.full_internal_transport μ (W 1) S (T 1) hS (hT 1)
    ((mT 1).trans hmS.symm) d hd (hf 1) hi1
  have hcount := ThirdsInternalCount.internal_count μ W hW bW hpart S hS d (ne_of_gt hd) hmS T hf
  have hout : ∀ᵐ u ∂μ, u∉S → ∀ c, Profile ν W r c u := by
    apply ThirdsOutsideProfiles.outside_rows μ W hW S hS d hd hmS T r
      (rowGood_ae μ W bW sW hpart) hf he0 he1 hcount
    intro σ hσ0 hσ1
    filter_upwards [hfamilies σ hσ0 hσ1] with u hu
    intro hmem
    rcases hu hmem with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hsum : ∀ᵐ p ∂ν.prod ν, W 0 p+W 1 p=1 := by
    have hsν : ∀ᵐ x ∂ν, x∈S := ThirdsNormalizedRestriction.conditional_ae μ S hS _
      (Filter.Eventually.of_forall (fun _ hx => hx))
    have hxy : ∀ᵐ p ∂ν.prod ν, p.1∈S ∧ p.2∈S := by
      apply (Measure.ae_prod_iff_ae_ae (hS.prod hS)).mpr
      filter_upwards [hsν] with x hx
      filter_upwards [hsν] with y hy
      exact ⟨hx,hy⟩
    filter_upwards [hCD.filter_mono hap.ae_le,hxy] with p hp hxy
    exact hp hxy.1 hxy.2
  have hrb : ∀ᵐ x ∂ν, r x=1 ∨ r x= -1 := by
    filter_upwards [hrX] with x hx
    rcases oneSet_binary X x with hh|hh
    · right; simpa only [hh,mul_zero,zero_sub] using hx
    · left; norm_num [hh] at hx ⊢; exact hx
  have hinν := ThirdsInternalProfiles.internal_rows ν W r e
    (fun c => ((bW c).filter_mono hap.ae_le).mono (fun _ h => h.1))
    (hpart.filter_mono hap.ae_le) hsum he hrb hCr
  have hin : ∀ᵐ u ∂μ, u∈S → ∀ c, Profile ν W r c u :=
    (ThirdsInternalProfiles.conditional_ae_iff μ S hS _).mp hinν
  refine ⟨X,r,hX,mX,hrm,hrX,?_⟩
  filter_upwards [hin,hout] with u hu hv
  by_cases hus : u∈S
  · exact hu hus
  · exact hv hus
end ThirdsCaseAProfiles
end JigBundleModule98

/- Inlined module ThirdsTwinExtraction; original SHA256 fe170067eced363cf4020329edb1f54641a720b558e50a4e5a50b9301191d176 -/
section JigBundleModule99
open MeasureTheory
namespace ThirdsTwinExtraction
open TwoPairHalfSetOperator ThirdsDeterministicTransport ThirdsOutsideProfiles
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma target_saturation (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ = d)
    (I T : Set Ω) (hI : MeasurableSet I) (hT : MeasurableSet T) (hm : μ.real T = d)
    (hp : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → 0 < C p → p.2 ∈ T) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → C p = oneSet T p.2 := by
  have hmeas : MeasurableSet {p : Ω × Ω | p.1∈I → C p=oneSet T p.2} :=
    (hI.preimage measurable_fst).imp
      (measurableSet_eq_fun hC ((oneSet_measurable T hT).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod bC,Measure.ae_ae_of_ae_prod hp,hr] with x bx px rx
  by_cases hx : x∈I
  · have hiC : Integrable (fun y => C (x,y)) μ :=
      LowSupportAnalysis.unit_integrable_ae (hC.comp (measurable_const.prodMk measurable_id)) bx
    have hiT : Integrable (oneSet T) μ := (integrable_const (1:ℝ)).indicator hT
    have hle : ∀ᵐ y ∂μ, C (x,y)≤oneSet T y := by
      filter_upwards [bx,px] with y byy pxy
      classical
      by_cases hy : y∈T
      · simpa [oneSet,hy] using byy.2
      · have hz : C (x,y)≤0 := le_of_not_gt (fun hh => hy (pxy hx hh))
        simpa [oneSet,hy] using hz
    have hz : (∫ y, oneSet T y-C (x,y) ∂μ)=0 := by
      rw [integral_sub hiT hiC,rx]
      simp [oneSet,integral_indicator hT,hm]
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (hle.mono fun _ h => sub_nonneg.mpr h) (hiT.sub hiC)).mp hz
    filter_upwards [he] with y hy
    intro _
    exact (sub_eq_zero.mp hy).symm
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hx h))

lemma endpoint_twin (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (sC : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (d : ℝ) (hd : d ≠ 0) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (I : Set Ω) (hI : MeasurableSet I) (hm : μ.real I=d)
    (hend : ∀ᵐ x ∂μ, (∫ y in I, C (x,y) ∂μ)=0 ∨ (∫ y in I, C (x,y) ∂μ)=d) :
    ∃ T : Set Ω, MeasurableSet T ∧ μ.real T=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈I → C p=oneSet T p.2) := by
  obtain ⟨T,hT,mT,hf,hb,hc⟩ := set_transport μ C hC bC sC d hd hr I hI hend
  refine ⟨T,hT,mT.trans hm,?_⟩
  apply target_saturation μ C hC bC d hr I T hI hT (mT.trans hm)
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  filter_upwards [hs,sC] with p hp hsym
  intro hx hpos
  have hh := hp (show 0<C (p.2,p.1) by rw [← hsym]; exact hpos)
  classical
  by_contra hy
  simp [oneSet,hx,hy] at hh

lemma profile_endpoints (W : Fin 6 → Ω × Ω → ℝ) (r : Ω → ℝ)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X)
    (d : ℝ) (hm : μ.real (X∩S)=d)
    (hrX : r =ᵐ[ProbabilityTheory.cond μ S] (fun x => 2*oneSet X x-1))
    (hp : ∀ᵐ u ∂μ, ∀ c, Profile (ProbabilityTheory.cond μ S) W r c u) :
    ∀ c, ∀ᵐ u ∂μ, (∫ y in X∩S, W c (u,y) ∂μ)=0 ∨
      (∫ y in X∩S, W c (u,y) ∂μ)=d := by
  intro c
  filter_upwards [hp] with u hu
  have convert (f : Ω → ℝ) (he : (fun y => W c (u,y)) =ᵐ[ProbabilityTheory.cond μ S] f)
      (a : ℝ) (hf : ∀ᵐ y ∂ProbabilityTheory.cond μ S, y∈X → f y=a) :
      (∫ y in X∩S, W c (u,y) ∂μ)=a*d := by
    have ha : ∀ᵐ y ∂ProbabilityTheory.cond μ S, y∈X → W c (u,y)=a := by
      filter_upwards [he,hf] with y hy hf
      intro hx
      exact hy.trans (hf hx)
    have hb := (ThirdsInternalProfiles.conditional_ae_iff μ S hS _).mp ha
    have hc : ∀ᵐ y ∂μ.restrict (X∩S), W c (u,y)=a := by
      apply (ae_restrict_iff' (hX.inter hS)).mpr
      filter_upwards [hb] with y hy
      intro hh
      exact hy hh.2 hh.1
    rw [integral_congr_ae hc]
    simp [hm, mul_comm]
  rcases hu c with hz|hplus|hminus
  · left
    simpa using convert (fun _ => 0) hz 0 (Filter.Eventually.of_forall (fun _ _ => rfl))
  · right
    have h : ∀ᵐ y ∂ProbabilityTheory.cond μ S, y∈X → (1+r y)/2=(1:ℝ) := by
      filter_upwards [hrX] with y hy
      intro hx
      simp [oneSet,hx] at hy
      linarith
    simpa using convert (fun y => (1+r y)/2) hplus 1 h
  · left
    have h : ∀ᵐ y ∂ProbabilityTheory.cond μ S, y∈X → (1-r y)/2=(0:ℝ) := by
      filter_upwards [hrX] with y hy
      intro hx
      simp [oneSet,hx] at hy
      linarith
    simpa using convert (fun y => (1-r y)/2) hminus 0 h

lemma profiles_twin (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (d : ℝ) (hd : 0<d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hm : μ.real (X∩S)=d)
    (r : Ω → ℝ) (hrX : r =ᵐ[ProbabilityTheory.cond μ S] (fun x => 2*oneSet X x-1))
    (hp : ∀ᵐ u ∂μ, ∀ c, Profile (ProbabilityTheory.cond μ S) W r c u) :
    ∀ c, ∃ T : Set Ω, MeasurableSet T ∧ μ.real T=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈X∩S → W c p=oneSet T p.2) := by
  intro c
  exact endpoint_twin μ (W c) (hW c) (bW c) (sW c) d (ne_of_gt hd) (hr c)
    (X∩S) (hX.inter hS) hm (profile_endpoints μ W r S X hS hX d hm hrX hp c)
end ThirdsTwinExtraction
end JigBundleModule99

/- Inlined module ThirdsRectangleBudget; original SHA256 c9bccb0ff2053a85025d189f99eed77dca656ed01d6f7678253c25fbf482e689 -/
section JigBundleModule100
open MeasureTheory
namespace ThirdsRectangleBudget
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma mass_le (C : Ω × Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p≤1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (A B : Set Ω) (hB : MeasurableSet B) (hA : 0<μ.real A)
    (hf : ∀ᵐ p ∂μ.prod μ, p.1∈A → p.2∈B → C p=1) : μ.real B≤d := by
  have hh : ∀ᵐ x ∂μ, x∈A → μ.real B≤d := by
    filter_upwards [Measure.ae_ae_of_ae_prod bC,Measure.ae_ae_of_ae_prod hf,hr] with x bx fx rx
    intro hx
    have hiC := LowSupportAnalysis.unit_integrable_ae (hC.comp (measurable_const.prodMk measurable_id)) bx
    have hiB : Integrable (oneSet B) μ := (integrable_const (1:ℝ)).indicator hB
    have hle : ∀ᵐ y ∂μ, oneSet B y≤C (x,y) := by
      filter_upwards [bx,fx] with y byy fxy
      classical
      by_cases hy : y∈B
      · simp [oneSet,hy,fxy hx hy]
      · simpa [oneSet,hy] using byy.1
    have hm := integral_mono_ae hiB hiC hle
    simpa [oneSet,integral_indicator hB,rx] using hm
  have hn : μ A≠0 := by
    intro hz
    have he : μ.real A=0 := by simp [measureReal_def,hz]
    linarith
  obtain ⟨x,hx,hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn (ae_restrict_of_ae hh)
  exact hp hx
end ThirdsRectangleBudget
end JigBundleModule100

/- Inlined module ThirdsCaseBForced; original SHA256 5ac045c8a34dbf878cf42e059d3b64dfbcd9b01bc08998d6fbd6a16a95e5f7c0 -/
section JigBundleModule101
open MeasureTheory
namespace ThirdsCaseBForced
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma conditional_set_integral (S X : Set Ω) (hX : MeasurableSet X) (f : Ω → ℝ) :
    (∫ x in X, f x ∂ProbabilityTheory.cond μ S)=
      (μ.real S)⁻¹*(∫ x in X∩S, f x ∂μ) := by
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_smul,Measure.restrict_restrict hX,integral_smul_measure]
  simp [measureReal_def,ENNReal.toReal_inv,smul_eq_mul]
lemma outside_active_opposite (C : Ω × Ω → ℝ) (hm : Measurable C)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (hs : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (S X T : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hc : ∀ᵐ p ∂μ.prod μ, p.1∈X → C p=oneSet X p.2)
    (ha : act μ C (oneSet S) =ᵐ[μ] (fun u => d*oneSet T u)) :
    ∀ᵐ u ∂μ, u∉S → u∈T →
      (fun x => C (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd mS
  have hac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have mxν : ν.real X=(1:ℝ)/2 := by
    rw [ThirdsNormalizedRestriction.conditional_real μ S X hX,Set.inter_eq_left.mpr hXS,mX,mS]
    field_simp
    <;> nlinarith
  have hz := ThirdsForcedHalfRow.full_clique_outside_zero μ C X hX hs hc
  filter_upwards [hz,ha,Measure.ae_ae_of_ae_prod hb] with u hzu hau bu
  intro hus hut
  have hun : u∉X := fun h => hus (hXS h)
  have mf : (∫ x, C (u,x) ∂ν)=(1:ℝ)/2 := by
    have huact : act μ C (oneSet S) u=d := by simpa [oneSet,hut] using hau
    rw [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ C S hS] at huact
    rw [ThirdsNormalizedRestriction.conditional_integral μ S,mS,huact]
    field_simp
    <;> nlinarith
  have zf : (∫ x in X, C (u,x) ∂ν)=0 := by
    rw [conditional_set_integral μ S X hX,Set.inter_eq_left.mpr hXS,hzu hun,mul_zero]
  exact ThirdsForcedHalfRow.zero_half_row ν (fun x => C (u,x))
    (hm.comp (measurable_const.prodMk measurable_id)) (bu.filter_mono hac.ae_le) mf X hX mxν zf
end ThirdsCaseBForced
open MeasureTheory
namespace ThirdsCaseBForced
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma forced_rectangles (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : d≠0) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T c) x))
    (hz : ∀ᵐ z ∂μ, z∈T 1∩T 2 → ∀ᵐ v ∂μ, v∈T 5 → W 0 (z,v)=0) :
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 5)\S → W 4 p=1) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 4∩T 5)\S → W 3 p=1) := by
  have ho (c : Fin 6) := ThirdsTransportSupport.outside_zero μ (W c) ((bW c).mono fun _ h => h.1)
    S (T c) (ThirdsTransportSupport.given_support μ (W c) (hW c) (bW c) (sW c) d hd (hr c) S (T c) hS (hf c))
  have hs (c : Fin 6) := Measure.measurePreserving_swap.quasiMeasurePreserving.ae (ho c)
  have haz : ∀ᵐ p ∂μ.prod μ, p.1∈T 1∩T 2 → p.2∈T 5 → W 0 p=0 := by
    apply (Measure.ae_prod_iff_ae_ae ((hT 1 |>.inter (hT 2) |>.preimage measurable_fst).imp
      ((hT 5 |>.preimage measurable_snd).imp (measurableSet_eq_fun (hW 0) measurable_const)))).mpr
    filter_upwards [hz] with x hx
    by_cases ht : x∈T 1∩T 2
    · filter_upwards [hx ht] with y hy
      exact fun _ => hy
    · exact Filter.Eventually.of_forall (fun _ hh => False.elim (ht hh))
  constructor
  · filter_upwards [ho 1,ho 2,hs 3,hs 5,sW 3,sW 5,haz,hpart] with p h1 h2 h3 h5 s3 s5 h0 hp
    intro hx hy
    have e0 := h0 hx.1 hy.1.2
    have e1 := h1 hx.1.1 hy.2
    have e2 := h2 hx.1.2 hy.2
    have e3 : W 3 p=0 := s3.trans (h3 hy.1.1 hx.2)
    have e5 : W 5 p=0 := s5.trans (h5 hy.1.2 hx.2)
    simpa [Fin.sum_univ_six,e0,e1,e2,e3,e5] using hp
  · filter_upwards [ho 1,ho 2,hs 4,hs 5,sW 4,sW 5,haz,hpart] with p h1 h2 h4 h5 s4 s5 h0 hp
    intro hx hy
    have e0 := h0 hx.1 hy.1.2
    have e1 := h1 hx.1.1 hy.2
    have e2 := h2 hx.1.2 hy.2
    have e4 : W 4 p=0 := s4.trans (h4 hy.1.1 hx.2)
    have e5 : W 5 p=0 := s5.trans (h5 hy.1.2 hx.2)
    simpa [Fin.sum_univ_six,e0,e1,e2,e4,e5] using hp
lemma forced_mass_bounds (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : d≠0) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun x => d*oneSet (T c) x))
    (hz : ∀ᵐ z ∂μ, z∈T 1∩T 2 → ∀ᵐ v ∂μ, v∈T 5 → W 0 (z,v)=0)
    (hp : 0<μ.real ((T 1∩T 2)\S)) :
    μ.real ((T 3∩T 5)\S)≤d ∧ μ.real ((T 4∩T 5)\S)≤d := by
  have h := forced_rectangles μ W hW bW sW hpart d hd hr S hS T hT hf hz
  exact ⟨ThirdsRectangleBudget.mass_le μ (W 4) (hW 4) (bW 4) d (hr 4)
    ((T 1∩T 2)\S) ((T 3∩T 5)\S) (((hT 3).inter (hT 5)).diff hS) hp h.1,
    ThirdsRectangleBudget.mass_le μ (W 3) (hW 3) (bW 3) d (hr 3)
    ((T 1∩T 2)\S) ((T 4∩T 5)\S) (((hT 4).inter (hT 5)).diff hS) hp h.2⟩
end ThirdsCaseBForced
end JigBundleModule101

/- Inlined module ThirdsAnchorForms; original SHA256 06a9a2e3d3d69e80bea23342087d7cc82377da47b0b523d86f346243358323f3 -/
section JigBundleModule102
open MeasureTheory
namespace ThirdsAnchorForms
open ThirdsRankOneComp TwoPairHalfSetOperator ThirdsCrossClique
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma centered_mixed (f r : Ω → ℝ) (hf : Measurable f) (hr : Measurable r)
    (he : f =ᵐ[μ] (fun x => (1+r x)/2)) :
    anchor r =ᵐ[μ.prod μ] mixed f := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (measurable_anchor r hr)
    (by unfold mixed; fun_prop))).mpr
  filter_upwards [he] with x hx
  filter_upwards [he] with y hy
  change (1-r x*r y)/2=f x*(1-f y)+(1-f x)*f y
  rw [hx,hy]
  ring
lemma centered_cross (r : Ω → ℝ) (hr : Measurable r) (X : Set Ω) (hX : MeasurableSet X)
    (he : (fun x => (1+r x)/2) =ᵐ[μ] (fun x => 1-oneSet X x)) :
    anchor r =ᵐ[μ.prod μ] cross X := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (measurable_anchor r hr)
    (by unfold cross; have h := oneSet_measurable X hX; fun_prop))).mpr
  filter_upwards [he] with x hx
  filter_upwards [he] with y hy
  change (1+r x)/2=1-oneSet X x at hx
  change (1+r y)/2=1-oneSet X y at hy
  have rx : r x=1-2*oneSet X x := by linarith
  have ry : r y=1-2*oneSet X y := by linarith
  change (1-r x*r y)/2=oneSet X x*(1-oneSet X y)+(1-oneSet X x)*oneSet X y
  rw [rx,ry]
  ring
end ThirdsAnchorForms
end JigBundleModule102

/- Inlined module ThirdsCaseBPairBinary; original SHA256 6b74cfc53f61a835e03eab251f4a5780795f43cf8fdc831d6fe06573b6aed27d -/
section JigBundleModule103
open MeasureTheory
namespace ThirdsCaseBPairBinary
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter ThirdsRankOneComp ThirdsCrossClique
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma pair_binary (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hclique : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (e0 : W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] cross X)
    (e2 : W 2 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] otherClique X)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hpos : μ (T 1∩T 5) ≠ 0) :
    ∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x)) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd mS
  have hac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have mxν : ν.real X=(1:ℝ)/2 := by
    rw [ThirdsNormalizedRestriction.conditional_real μ S X hX,Set.inter_eq_left.mpr hXS,mX,mS]
    field_simp
    <;> nlinarith
  have hSpos : μ S ≠ 0 := by
    intro h
    have hh : μ.real S=0 := by simp [measureReal_def,h]
    linarith
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,2,3,4,1,5] (by decide)
  have hzσ : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have hzero := ThirdsAEAnchors.canonical_anchor_zeros μ (fun c => W (σ c))
    (fun c => hW (σ c)) (fun c => bW (σ c)) (fun c => sW (σ c)) hzσ S hS hSpos
  have hzuv : ∀ᵐ u ∂μ, ∀ᵐ v ∂μ, cycle4 ν (W 0) (W 2)
      (ThirdsCanonicalAnchors.bridge W 1 5 v) (ThirdsCanonicalAnchors.bridge W 3 4 u)=0 := by
    filter_upwards [hzero] with u hu
    filter_upwards [hu] with v hv
    exact hv.1
  have hvout : ∀ᵐ v ∂μ, v∈T 1∩T 5 → v∉S := by
    filter_upwards [h0,hc] with v hv0 hvc
    intro hv hvs
    have h1 : oneSet (T 1) v=1 := by simp [oneSet,hv.1]
    have h5 : oneSet (T 5) v=1 := by simp [oneSet,hv.2]
    have hz0 : oneSet (T 0) v=1 := by rw [hv0]; simp [oneSet,hvs]
    simp only [Fin.sum_univ_six] at hvc
    nlinarith [(oneSet_bounds (T 2) v).1,(oneSet_bounds (T 3) v).1,(oneSet_bounds (T 4) v).1]
  have hvforced := ThirdsCaseBForced.outside_active_opposite μ (W 1) (hW 1) (bW 1) (sW 1)
    S X (T 1) hS hX hXS d hd mS mX hclique (hf 1)
  have hRG := rowGood_ae μ W bW sW hpart
  have hact := ae_all_iff.mpr hf
  filter_upwards [hzuv,hRG,hact] with u hzu hgu hau
  intro hu
  have hg : ∀ᵐ v ∂μ, RowGood μ W v ∧
      (∀ c, act μ (W c) (oneSet S) v=d*oneSet (T c) v) ∧
      (v∈T 1∩T 5 → v∉S) ∧
      (v∉S → v∈T 1 → (fun x => W 1 (v,x)) =ᵐ[ν] (fun x => 1-oneSet X x)) ∧
      cycle4 ν (W 0) (W 2) (ThirdsCanonicalAnchors.bridge W 1 5 v) (ThirdsCanonicalAnchors.bridge W 3 4 u)=0 := by
    filter_upwards [hRG,hact,hvout,hvforced,hzu] with v hg ha ho hf hz
    exact ⟨hg,ha,ho,hf,hz⟩
  obtain ⟨v,hv,hgv,hav,hov,hfv,hzv⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hg)
  have mui (c : Fin 6) (hc : u∈T c) : act μ (W c) (oneSet S) u=d := by rw [hau c]; simp [oneSet,hc]
  have mvi (c : Fin 6) (hc : v∈T c) : act μ (W c) (oneSet S) v=d := by rw [hav c]; simp [oneSet,hc]
  obtain ⟨r,hr,br,mr,er,_,ebr⟩ := selected_center μ W hW S hS d hd mS u hgu 3 4 (by decide) (mui _ hu.1) (mui _ hu.2)
  obtain ⟨t,ht,bt,mt,et,_,ebt⟩ := selected_center μ W hW S hS d hd mS v hgv 1 5 (by decide) (mvi _ hv.1) (mvi _ hv.2)
  have evt : ThirdsCanonicalAnchors.bridge W 1 5 v =ᵐ[ν.prod ν] cross X :=
    ebt.trans (ThirdsAnchorForms.centered_cross ν t ht X hX (et.symm.trans (hfv (hov hv) hv.1)))
  have eur : ThirdsCanonicalAnchors.bridge W 3 4 u =ᵐ[ν.prod ν] mixed (fun x => W 3 (u,x)) :=
    ebr.trans (ThirdsAnchorForms.centered_mixed ν (fun x => W 3 (u,x)) r (by fun_prop) hr er)
  have z : cycle4 ν (cross X) (otherClique X) (cross X) (mixed (fun x => W 3 (u,x)))=0 := by
    rw [← cycle4_congr ν e0 e2 evt eur]
    exact hzv
  have mf : (∫ x, W 3 (u,x) ∂ν)=(1:ℝ)/2 := by
    have hh := mui 3 hu.1
    rw [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ (W 3) S hS] at hh
    rw [ThirdsNormalizedRestriction.conditional_integral μ S,mS,hh]
    field_simp
    <;> nlinarith
  exact ThirdsCrossClique.zero_forces_binary ν X hX mxν (fun x => W 3 (u,x)) (by fun_prop)
    (((hgu.1 3).filter_mono hac.ae_le).mono fun _ h => ⟨h.1,h.2.1⟩) mf z
end ThirdsCaseBPairBinary
end JigBundleModule103

/- Inlined module ThirdsCaseBPeripheral; original SHA256 da8b92e499ad728adab356a2d4cc563a25423ee4a916760f3c0cd7de2903d0e6 -/
section JigBundleModule104
open MeasureTheory
namespace ThirdsCaseBPeripheral
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter ThirdsRankOneComp ThirdsCrossClique
open Submissions.E811FourColorParity.Representatives
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma mixing_null (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hclique : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (e0 : W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] cross X)
    (e2 : W 2 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] otherClique X)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x)))) : μ (T 1∩T 5)=0 := by
  by_contra hp
  exact hn (ThirdsCaseBPairBinary.pair_binary μ W hW bW sW hpart S X hS hX hXS d hd mS mX T hf h0 hc hclique e0 e2 hz hp)
lemma both_null (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hclique : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hclique2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (e1 : W 1 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] otherClique (S\X))
    (e0 : W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] cross X)
    (e2 : W 2 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] otherClique X)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x)))) : μ (T 1∩T 5)=0 ∧ μ (T 2∩T 5)=0 := by
  have nb := mixing_null μ W hW bW sW hpart S X hS hX hXS d hd mS mX T hf h0 hc hclique e0 e2 hz hn
  let ν := ProbabilityTheory.cond μ S
  have ey : oneSet (S\X) =ᵐ[ν] (fun x => 1-oneSet X x) := by
    apply ThirdsNormalizedRestriction.conditional_ae μ S hS
    exact Filter.Eventually.of_forall (fun x hx => by
      by_cases hxx : x∈X <;> simp [oneSet,hx,hxx])
  have ecross : cross X =ᵐ[ν.prod ν] cross (S\X) := by
    have hx : Measurable (oneSet X) := oneSet_measurable X hX
    have hy : Measurable (oneSet (S\X)) := oneSet_measurable (S\X) (hS.diff hX)
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by unfold cross; fun_prop) (by unfold cross; fun_prop))).mpr
    filter_upwards [ey] with x ex
    filter_upwards [ey] with y ey
    simp only [cross]
    rw [ex,ey]
    ring
  have hnY : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ν] oneSet (S\X)) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ν] (fun x => 1-oneSet (S\X) x))) := by
    intro hh
    apply hn
    filter_upwards [hh] with u hu
    intro ht
    rcases hu ht with h | h
    · exact Or.inr (h.trans ey)
    · apply Or.inl
      filter_upwards [h,ey] with x hx ex
      rw [hx,ex]
      ring
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,2,1,3,4,5] (by decide)
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have count : ∀ᵐ u ∂μ, ∑ c, oneSet (T (σ c)) u=2 := by
    filter_upwards [hc] with u hu
    rw [Equiv.sum_comp σ (fun c => oneSet (T c) u)]; exact hu
  have hzσ : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have nc := mixing_null μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) part S (S\X) hS hY Set.sdiff_subset
    d hd mS mY (fun c => T (σ c)) (fun c => hf (σ c)) h0 count hclique2
    (e0.trans ecross) e1 hzσ hnY
  exact ⟨nb,nc⟩
end ThirdsCaseBPeripheral
end JigBundleModule104

/- Inlined module ThirdsCaseBLayout; original SHA256 e441ec8364eac503ee40b606ac3ab09180154f6eef76575226c31965f361e63c -/
section JigBundleModule105
open MeasureTheory
namespace ThirdsCaseBLayout
open TwoPairHalfSetOperator ThirdsLiteralLayout
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma complementary_set (S X Y : Set Ω) (hXS : X⊆S) (hYS : Y⊆S)
    (hdis : μ.real (X∩Y)=0) (hcover : oneSet (X∪Y) =ᵐ[μ] oneSet S) :
    Y =ᵐ[μ] S\X := by
  have hz := null_indicator μ (X∩Y) hdis
  filter_upwards [hz,hcover] with x hx hc
  apply propext
  change x∈Y ↔ x∈S ∧ x∉X
  constructor
  · intro hy
    refine ⟨hYS hy,?_⟩
    intro hxx
    simp [oneSet,hxx,hy] at hx
  · rintro ⟨hs,hn⟩
    by_contra hy
    simp [oneSet,hs,hn,hy] at hc
lemma indicator_congr {X Y : Set Ω} (he : X =ᵐ[μ] Y) : oneSet X =ᵐ[μ] oneSet Y := by
  filter_upwards [he] with x hx
  have h : x∈X ↔ x∈Y := Iff.of_eq hx
  by_cases hx : x∈X
  · have hy := h.mp hx; simp [oneSet,hx,hy]
  · have hy : x∉Y := fun hy => hx (h.mpr hy)
    simp [oneSet,hx,hy]
lemma row_set_congr (C : Ω×Ω → ℝ) (hC : Measurable C)
    (X Y : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (he : X =ᵐ[μ] Y)
    (hr : ∀ᵐ p ∂μ.prod μ, p.1∈X → C p=oneSet X p.2) :
    ∀ᵐ p ∂μ.prod μ, p.1∈Y → C p=oneSet Y p.2 := by
  have hm : MeasurableSet {p : Ω×Ω | p.1∈Y → C p=oneSet Y p.2} :=
    (hY.preimage measurable_fst).imp (measurableSet_eq_fun hC ((oneSet_measurable Y hY).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [he,Measure.ae_ae_of_ae_prod hr] with x hx hrow
  filter_upwards [indicator_congr μ he,hrow] with y hy hxy
  intro hxs
  have hxx : x∈X := (Iff.of_eq hx).mpr hxs
  exact (hxy hxx).trans hy

lemma normalized_cross (C : Ω×Ω → ℝ) (hC : Measurable C)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X)
    (hx : ∀ᵐ p ∂μ.prod μ, p.1∈X → C p=oneSet (S\X) p.2)
    (hy : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → C p=oneSet X p.2) :
    C =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] ThirdsCrossClique.cross X := by
  have hi : Measurable (oneSet X) := oneSet_measurable X hX
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hC (by unfold ThirdsCrossClique.cross; fun_prop))).mpr
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [Measure.ae_ae_of_ae_prod hx,Measure.ae_ae_of_ae_prod hy] with x hxr hyr
  intro xs
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [hxr,hyr] with y hxy hyy
  intro ys
  by_cases xx : x∈X
  · rw [hxy xx]
    by_cases yy : y∈X <;> simp [ThirdsCrossClique.cross,oneSet,xx,yy,ys]
  · rw [hyy ⟨xs,xx⟩]
    by_cases yy : y∈X <;> simp [ThirdsCrossClique.cross,oneSet,xx,yy,ys]
lemma normalized_clique (C D : Ω×Ω → ℝ) (hC : Measurable C)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X)
    (sym : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (bc : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p+D p≤1)
    (hx : ∀ᵐ p ∂μ.prod μ, p.1∈X → C p=oneSet X p.2)
    (hy : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → D p=oneSet (S\X) p.2) :
    C =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] ThirdsCrossClique.otherClique (S\X) := by
  have hi : Measurable (oneSet (S\X)) := oneSet_measurable (S\X) (hS.diff hX)
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hx
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hC (by unfold ThirdsCrossClique.otherClique; fun_prop))).mpr
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [Measure.ae_ae_of_ae_prod hx,Measure.ae_ae_of_ae_prod hy,
    Measure.ae_ae_of_ae_prod hs,Measure.ae_ae_of_ae_prod sym,Measure.ae_ae_of_ae_prod bc] with x hxr hyr hsr hsym hb
  intro xs
  apply ThirdsNormalizedRestriction.conditional_ae μ S hS
  filter_upwards [hxr,hyr,hsr,hsym,hb] with y hxy hyy hsy hsym hb
  intro ys
  by_cases xx : x∈X
  · rw [hxy xx]
    by_cases yy : y∈X <;> simp [ThirdsCrossClique.otherClique,oneSet,xx,yy,xs,ys]
  · by_cases yy : y∈X
    · change y∈X → C (y,x)=oneSet X x at hsy
      rw [hsym,hsy yy]
      simp [ThirdsCrossClique.otherClique,oneSet,xx,yy,xs,ys]
    · have ed : D (x,y)=1 := by simpa [oneSet,ys,yy] using hyy ⟨xs,xx⟩
      have ec : C (x,y)=0 := by linarith
      rw [ec]
      simp [ThirdsCrossClique.otherClique,oneSet,xx,yy,xs,ys]

lemma six_forms (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (hb : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hc : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2) :
    (W 0 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] ThirdsCrossClique.cross X) ∧
    (W 1 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] ThirdsCrossClique.otherClique (S\X)) ∧
    (W 2 =ᵐ[(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ S)] ThirdsCrossClique.otherClique X) := by
  have bc : ∀ᵐ p ∂μ.prod μ, 0≤W 1 p ∧ W 1 p+W 2 p≤1 := by
    filter_upwards [bW 0,bW 1,bW 2,bW 3,bW 4,bW 5,hpart] with p h0 h1 h2 h3 h4 h5 hp
    simp only [Fin.sum_univ_six] at hp
    exact ⟨h1.1,by linarith⟩
  have cb : ∀ᵐ p ∂μ.prod μ, 0≤W 2 p ∧ W 2 p+W 1 p≤1 := by
    filter_upwards [bc,bW 2] with p hp h2
    exact ⟨h2.1,by linarith [hp.2]⟩
  have hXX : S\(S\X)=X := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hs,hn⟩; by_contra hx; exact hn ⟨hs,hx⟩
    · intro hx; exact ⟨hXS hx,fun h => h.2 hx⟩
  have hc' := normalized_clique μ (W 2) (W 1) (hW 2) S (S\X) hS (hS.diff hX) (sW 2) cb hc
    (by simpa only [hXX] using hb)
  exact ⟨normalized_cross μ (W 0) (hW 0) S X hS hX haX haY,
    normalized_clique μ (W 1) (W 2) (hW 1) S X hS hX (sW 1) bc hb hc,
    by simpa only [hXX] using hc'⟩
end ThirdsCaseBLayout
end JigBundleModule105

/- Inlined module ThirdsCaseATwin; original SHA256 07ce38e7c36445a4d77e7979cc038df2ccc3698ae7a23c06ee2f80567bb6cb68 -/
section JigBundleModule106
open MeasureTheory
namespace ThirdsCaseATwin
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter ThirdsOutsideProfiles
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma case_a_twin (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0 < d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (hmS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d)
    (hi0 : ∀ᵐ x ∂μ, x∈S → act μ (W 0) (oneSet S) x=d)
    (hi1 : ∀ᵐ x ∂μ, x∈S → act μ (W 1) (oneSet S) x=d)
    (hCD : ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W 0 p+W 1 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0) :
    ∃ I : Set Ω, MeasurableSet I ∧ μ.real I=d ∧
      ∀ c, ∃ T : Set Ω, MeasurableSet T ∧ μ.real T=d ∧
        (∀ᵐ p ∂μ.prod μ, p.1∈I → W c p=oneSet T p.2) := by
  obtain ⟨X,r,hX,hmX,hrm,hrX,hp⟩ := ThirdsCaseAProfiles.case_a_profiles
    μ W hW bW sW hpart d hd hr S hS hmS hend hi0 hi1 hCD hz
  exact ⟨X∩S,hX.inter hS,hmX,
    ThirdsTwinExtraction.profiles_twin μ W hW bW sW d hd hr S X hS hX hmX r hrX hp⟩
end ThirdsCaseATwin
end JigBundleModule106

/- Inlined module ThirdsNormalizedStarting; original SHA256 a3b22c44d9ce900e35ac6117a7eeb2ee4a2610df532827c8f20ed101b78076c0 -/
section JigBundleModule107
open MeasureTheory
namespace ThirdsNormalizedStarting
open TwoPairHalfSetOperator ThirdsLiteralLayout
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma two_labels (a b : Fin 6) (hab : a≠b) :
    ∃ σ : Equiv.Perm (Fin 6), σ 0=a ∧ σ 1=b := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin 2 => (![0,1] : Fin 2 → Fin 6) i)
    (![a,b]) (by decide) (by intro i j; fin_cases i <;> fin_cases j <;> simp_all [ne_comm])
  exact ⟨σ,hσ 0,hσ 1⟩
lemma three_labels (a b g : Fin 6) (hab : a≠b) (hag : a≠g) (hbg : b≠g) :
    ∃ σ : Equiv.Perm (Fin 6), σ 0=g ∧ σ 1=a ∧ σ 2=b := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin 3 => (![0,1,2] : Fin 3 → Fin 6) i)
    (![g,a,b]) (by decide) (by intro i j; fin_cases i <;> fin_cases j <;> simp_all [ne_comm])
  exact ⟨σ,hσ 0,hσ 1,hσ 2⟩

structure AData (W : Fin 6 → Ω×Ω → ℝ) (S : Set Ω) (d : ℝ) where
  σ : Equiv.Perm (Fin 6)
  hi0 : ∀ᵐ x ∂μ, x∈S → act μ (W (σ 0)) (oneSet S) x=d
  hi1 : ∀ᵐ x ∂μ, x∈S → act μ (W (σ 1)) (oneSet S) x=d
  hCD : ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W (σ 0) p+W (σ 1) p=1
structure BData (W : Fin 6 → Ω×Ω → ℝ) (S : Set Ω) (d : ℝ) where
  σ : Equiv.Perm (Fin 6)
  X : Set Ω
  hX : MeasurableSet X
  hXS : X⊆S
  mX : μ.real X=d
  T : Fin 6 → Set Ω
  hT : ∀ c, MeasurableSet (T c)
  hm : ∀ c, μ.real (T c)=2*d
  hf : ∀ c, act μ (W (σ c)) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u)
  h0 : oneSet (T 0) =ᵐ[μ] oneSet S
  hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2
  hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W (σ 1) p=oneSet X p.2
  hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W (σ 2) p=oneSet (S\X) p.2
  haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W (σ 0) p=oneSet (S\X) p.2
  haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W (σ 0) p=oneSet X p.2
  mb : μ.real (S∩T 1)=d
  mc : μ.real (S∩T 2)=d
  mD : μ.real (S∩T 3)=0
  mE : μ.real (S∩T 4)=0
  mF : μ.real (S∩T 5)=0

lemma normalize (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0<d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d) :
    Nonempty (AData μ W S d) ∨ Nonempty (BData μ W S d) := by
  obtain ⟨T,hT,hmT,hf,hm,hclique,hcases⟩ := ThirdsInternalArrangement.arrangement_counts
    μ W hW bW sW hpart d hd hr S hS mS hend
  have count := ThirdsInternalCount.internal_count μ W hW bW hpart S hS d (ne_of_gt hd) mS T hf
  rcases ThirdsArrangementLabels.labels (fun c => μ.real (S∩T c)) d hd hm hcases with h | h
  · obtain ⟨a,b,hab,ma,mb,hzero⟩ := h
    obtain ⟨σ,s0,s1⟩ := two_labels a b hab
    have hi0 := ThirdsStartingDichotomy.global_internal_act μ (W a) S (T a) hS (hT a) d (ma.trans mS.symm) (hf a)
    have hi1 := ThirdsStartingDichotomy.global_internal_act μ (W b) S (T b) hS (hT b) d (mb.trans mS.symm) (hf b)
    have hz : ∀ c, c≠a → c≠b → ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈S → W c p=0 := by
      intro c ca cb
      exact zero_internal_kernel μ (W c) (hW c) (bW c) S (T c) hS d (hf c) (hzero c ca cb)
    have hCD := ThirdsStartingDichotomy.two_color_sum μ W S hpart a b hab hz
    exact Or.inl ⟨⟨σ,by simpa only [s0] using hi0,by simpa only [s1] using hi1,
      by simpa only [s0,s1] using hCD⟩⟩
  · obtain ⟨a,b,g,hab,hag,hbg,ma,mb,mg,hzero⟩ := h
    obtain ⟨σ,s0,s1,s2⟩ := three_labels a b g hab hag hbg
    let X := S∩T a
    let Y := S∩T b
    have hX : MeasurableSet X := hS.inter (hT a)
    have hY : MeasurableSet Y := hS.inter (hT b)
    have xs : X⊆S := Set.inter_subset_left
    have ys : Y⊆S := Set.inter_subset_left
    obtain ⟨hcover,hdis,hga,hgb⟩ := ThirdsLayoutCoupling.three_label_layout
      μ W hW bW sW hpart d hr S hS mS T hT hf a b g hab hag hbg ma mb hzero
      (hclique a ma) (hclique b mb)
    have eY : Y =ᵐ[μ] S\X := ThirdsCaseBLayout.complementary_set μ S X Y xs ys hdis hcover
    have eiY := ThirdsCaseBLayout.indicator_congr μ eY
    have e0 : oneSet (T g) =ᵐ[μ] oneSet S := by
      have es := full_subset_indicator μ (S∩T g) S (hS.inter (hT g)) Set.inter_subset_left (mg.trans mS.symm)
      have et := full_subset_indicator μ (S∩T g) (T g) (hS.inter (hT g)) Set.inter_subset_right
        (mg.trans ((hmT g).trans mS).symm)
      exact et.symm.trans es
    have hb : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W b p=oneSet (S\X) p.2 :=
      ThirdsCaseBLayout.row_set_congr μ (W b) (hW b) Y (S\X) hY (hS.diff hX) eY (hclique b mb)
    have gx : ∀ᵐ p ∂μ.prod μ, p.1∈X → W g p=oneSet (S\X) p.2 := by
      filter_upwards [hga,(Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae eiY] with p hp he
      exact fun hx => (hp hx).trans he
    have gy : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W g p=oneSet X p.2 := by
      filter_upwards [hgb,(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae eY] with p hp he
      exact fun hx => hp ((Iff.of_eq he).mpr hx)
    have cnt : ∀ᵐ u ∂μ, ∑ c, oneSet (T (σ c)) u=2 := by
      filter_upwards [count] with u hu
      rw [Equiv.sum_comp σ (fun c => oneSet (T c) u)]; exact hu
    have mz (i : Fin 6) (i0 : i≠0) (i1 : i≠1) (i2 : i≠2) : μ.real (S∩T (σ i))=0 := by
      apply hzero
      · intro h; exact i1 (σ.injective (h.trans s1.symm))
      · intro h; exact i2 (σ.injective (h.trans s2.symm))
      · intro h; exact i0 (σ.injective (h.trans s0.symm))
    refine Or.inr ⟨⟨σ,X,hX,xs,ma,(fun c => T (σ c)),(fun c => hT (σ c)),
      (fun c => (hmT (σ c)).trans mS),(fun c => hf (σ c)),?_,cnt,?_,?_,?_,?_,?_,?_,
      mz 3 (by decide) (by decide) (by decide),mz 4 (by decide) (by decide) (by decide),
      mz 5 (by decide) (by decide) (by decide)⟩⟩
    · simpa only [s0] using e0
    · simpa only [s1] using hclique a ma
    · simpa only [s2] using hb
    · simpa only [s0] using gx
    · simpa only [s0] using gy
    · simpa only [s1] using ma
    · simpa only [s2] using mb
end ThirdsNormalizedStarting
end JigBundleModule107

/- Inlined module ThirdsPairMasses; original SHA256 a03a14c17f26a410247745b47320b82fdb44e3e00e5c8e63cc046e7dd8a3b82c -/
section JigBundleModule108
namespace ThirdsPairMasses
variable (d z bD bE bF cD cE cF h i j : ℝ)
variable (hn : 0 ≤ z ∧ 0 ≤ bD ∧ 0 ≤ bE ∧ 0 ≤ bF ∧ 0 ≤ cD ∧ 0 ≤ cE ∧ 0 ≤ cF ∧ 0 ≤ h ∧ 0 ≤ i ∧ 0 ≤ j)
variable (rb : z+bD+bE+bF = d) (rc : z+cD+cE+cF = d)
variable (rD : bD+cD+h+i = 2*d) (rE : bE+cE+h+j = 2*d)
variable (rF : bF+cF+i+j = 2*d)

include hn rb rc rD rE rF

lemma one_mixing (hbF : bF = 0) (hcF : cF = 0) :
    h = z ∧ i+j = 2*d ∧ z ≤ d ∧ z ≤ i ∧ z ≤ j :=  by
  rcases hn with ⟨hz,hbD,hbE,hbF',hcD,hcE,hcF',hh,hi,hj⟩
  have hhZ : h = z :=  by linarith
  refine ⟨hhZ,by linarith,by linarith,?_,?_⟩ <;> linarith

lemma one_mixing_saturated (hbF : bF = 0) (hcF : cF = 0) (hi : i ≤ d) (hj : j ≤ d) :
    h = z ∧ i = d ∧ j = d ∧ bD+cD = d-z ∧ bE+cE = d-z ∧ bD = cE ∧ bE = cD :=  by
  have hs : i+j = 2*d :=  by linarith
  have hi' : i = d :=  by linarith
  have hj' : j = d :=  by linarith
  have hh : h = z :=  by linarith
  exact ⟨hh,hi',hj',by linarith,by linarith,by linarith,by linarith⟩

lemma two_mixing (hbF : bF = 0) (hcF : cF = 0) (hbE : bE = 0) (hcE : cE = 0) :
    h = z ∧ i = z ∧ j = 2*d-z ∧ bD = d-z ∧ cD = d-z ∧ bD+cD = 2*d-2*z ∧ z ≤ d :=  by
  rcases hn with ⟨hz,hbD,hbE',hbF',hcD,hcE',hcF',hh,hi,hj⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

lemma two_mixing_saturated (hbF : bF = 0) (hcF : cF = 0) (hbE : bE = 0) (hcE : cE = 0)
    (hj : j ≤ d) : z = d ∧ h = d ∧ i = d ∧ j = d ∧ bD = 0 ∧ cD = 0 :=  by
  rcases hn with ⟨hz,hbD,hbE',hbF',hcD,hcE',hcF',hh,hi,hj'⟩
  have hz' : z = d :=  by linarith
  exact ⟨hz',by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma three_mixing (hbD : bD = 0) (hbE : bE = 0) (hbF : bF = 0)
    (hcD : cD = 0) (hcE : cE = 0) (hcF : cF = 0) :
    z = d ∧ h = d ∧ i = d ∧ j = d :=  by
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

end ThirdsPairMasses
end JigBundleModule108

/- Inlined module ThirdsFiveIncidence; original SHA256 1633795dcfbe211ed87b9fdfc23848ae2b976317c898468920e726ebde12a37a -/
section JigBundleModule109
open MeasureTheory
namespace ThirdsFiveIncidence
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma binary_degree (a b c d e : ℝ) (ha : a=0 ∨ a=1)
    (ht : a+b+c+d+e=0 ∨ a+b+c+d+e=2)
    (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e) : a*(b+c+d+e)=a := by
  rcases ha with ha|ha
  · simp [ha]
  · rcases ht with ht|ht <;> nlinarith
lemma degree_mass (A B C D E : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D) (hE : MeasurableSet E)
    (he : ∀ᵐ x ∂μ, oneSet A x*(oneSet B x+oneSet C x+oneSet D x+oneSet E x)=oneSet A x) :
    μ.real (A∩B)+μ.real (A∩C)+μ.real (A∩D)+μ.real (A∩E)=μ.real A := by
  have ints (X Y : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y) :
      Integrable (fun x => oneSet X x*oneSet Y x) μ :=
    unit_integrable μ _ ((oneSet_measurable X hX).mul (oneSet_measurable Y hY))
      (fun x => mul_unit (oneSet_bounds X x) (oneSet_bounds Y x))
  have he' : (fun x => oneSet A x*oneSet B x+oneSet A x*oneSet C x+
      oneSet A x*oneSet D x+oneSet A x*oneSet E x)=ᵐ[μ] oneSet A := by
    filter_upwards [he] with x hx
    nlinarith
  have hi := integral_congr_ae he'
  rw [integral_add (f := fun x => oneSet A x*oneSet B x+oneSet A x*oneSet C x+oneSet A x*oneSet D x) (g := fun x => oneSet A x*oneSet E x) ((ints A B hA hB).add (ints A C hA hC) |>.add (ints A D hA hD)) (ints A E hA hE),
    integral_add (f := fun x => oneSet A x*oneSet B x+oneSet A x*oneSet C x) (g := fun x => oneSet A x*oneSet D x) ((ints A B hA hB).add (ints A C hA hC)) (ints A D hA hD),
    integral_add (f := fun x => oneSet A x*oneSet B x) (g := fun x => oneSet A x*oneSet C x) (ints A B hA hB) (ints A C hA hC),
    ThirdsPairMass.indicator_pair_integral μ A B hA hB,
    ThirdsPairMass.indicator_pair_integral μ A C hA hC,
    ThirdsPairMass.indicator_pair_integral μ A D hA hD,
    ThirdsPairMass.indicator_pair_integral μ A E hA hE] at hi
  simpa [oneSet,integral_indicator hA] using hi
lemma five_rows (U : Fin 5 → Set Ω) (hU : ∀ i, MeasurableSet (U i))
    (hc : ∀ᵐ x ∂μ, (∑ i, oneSet (U i) x)=0 ∨ (∑ i, oneSet (U i) x)=2) :
    (μ.real (U 0∩U 1)+μ.real (U 0∩U 2)+μ.real (U 0∩U 3)+μ.real (U 0∩U 4)=μ.real (U 0)) ∧
    (μ.real (U 0∩U 1)+μ.real (U 1∩U 2)+μ.real (U 1∩U 3)+μ.real (U 1∩U 4)=μ.real (U 1)) ∧
    (μ.real (U 0∩U 2)+μ.real (U 1∩U 2)+μ.real (U 2∩U 3)+μ.real (U 2∩U 4)=μ.real (U 2)) ∧
    (μ.real (U 0∩U 3)+μ.real (U 1∩U 3)+μ.real (U 2∩U 3)+μ.real (U 3∩U 4)=μ.real (U 3)) ∧
    (μ.real (U 0∩U 4)+μ.real (U 1∩U 4)+μ.real (U 2∩U 4)+μ.real (U 3∩U 4)=μ.real (U 4)) := by
  have hc' : ∀ᵐ x ∂μ, oneSet (U 0) x+oneSet (U 1) x+oneSet (U 2) x+oneSet (U 3) x+oneSet (U 4) x=0 ∨
      oneSet (U 0) x+oneSet (U 1) x+oneSet (U 2) x+oneSet (U 3) x+oneSet (U 4) x=2 := by
    simpa only [Fin.sum_univ_five] using hc
  have h0 := degree_mass μ (U 0) (U 1) (U 2) (U 3) (U 4) (hU 0) (hU 1) (hU 2) (hU 3) (hU 4) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ _ (oneSet_binary _ _)
    · rcases hx with hx|hx
      · left; linarith
      · right; linarith
    · exact (oneSet_bounds (U 1) x).1
    · exact (oneSet_bounds (U 2) x).1
    · exact (oneSet_bounds (U 3) x).1
    · exact (oneSet_bounds (U 4) x).1)
  have h1 := degree_mass μ (U 1) (U 0) (U 2) (U 3) (U 4) (hU 1) (hU 0) (hU 2) (hU 3) (hU 4) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ _ (oneSet_binary _ _)
    · rcases hx with hx|hx
      · left; linarith
      · right; linarith
    · exact (oneSet_bounds (U 0) x).1
    · exact (oneSet_bounds (U 2) x).1
    · exact (oneSet_bounds (U 3) x).1
    · exact (oneSet_bounds (U 4) x).1)
  simp only [Set.inter_comm (U 1) (U 0)] at h1
  have h2 := degree_mass μ (U 2) (U 0) (U 1) (U 3) (U 4) (hU 2) (hU 0) (hU 1) (hU 3) (hU 4) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ _ (oneSet_binary _ _)
    · rcases hx with hx|hx
      · left; linarith
      · right; linarith
    · exact (oneSet_bounds (U 0) x).1
    · exact (oneSet_bounds (U 1) x).1
    · exact (oneSet_bounds (U 3) x).1
    · exact (oneSet_bounds (U 4) x).1)
  simp only [Set.inter_comm (U 2) (U 0), Set.inter_comm (U 2) (U 1)] at h2
  have h3 := degree_mass μ (U 3) (U 0) (U 1) (U 2) (U 4) (hU 3) (hU 0) (hU 1) (hU 2) (hU 4) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ _ (oneSet_binary _ _)
    · rcases hx with hx|hx
      · left; linarith
      · right; linarith
    · exact (oneSet_bounds (U 0) x).1
    · exact (oneSet_bounds (U 1) x).1
    · exact (oneSet_bounds (U 2) x).1
    · exact (oneSet_bounds (U 4) x).1)
  simp only [Set.inter_comm (U 3) (U 0), Set.inter_comm (U 3) (U 1), Set.inter_comm (U 3) (U 2)] at h3
  have h4 := degree_mass μ (U 4) (U 0) (U 1) (U 2) (U 3) (hU 4) (hU 0) (hU 1) (hU 2) (hU 3) (by
    filter_upwards [hc'] with x hx
    apply binary_degree _ _ _ _ _ (oneSet_binary _ _)
    · rcases hx with hx|hx
      · left; linarith
      · right; linarith
    · exact (oneSet_bounds (U 0) x).1
    · exact (oneSet_bounds (U 1) x).1
    · exact (oneSet_bounds (U 2) x).1
    · exact (oneSet_bounds (U 3) x).1)
  simp only [Set.inter_comm (U 4) (U 0), Set.inter_comm (U 4) (U 1), Set.inter_comm (U 4) (U 2), Set.inter_comm (U 4) (U 3)] at h4
  exact ⟨h0,h1,h2,h3,h4⟩
lemma outside_count (T : Fin 6 → Set Ω) (S : Set Ω)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, ∑ i, oneSet (T i) x=2) :
    ∀ᵐ x ∂μ, (∑ i : Fin 5, oneSet (T i.succ\S) x)=0 ∨
      (∑ i : Fin 5, oneSet (T i.succ\S) x)=2 := by
  filter_upwards [h0,hc] with x hx hcount
  classical
  by_cases hs : x∈S
  · left; simp [oneSet,hs]
  · right
    have hz : oneSet (T 0) x=0 := by rw [hx]; simp [oneSet,hs]
    simp only [Fin.sum_univ_six,hz,zero_add] at hcount
    have he (i : Fin 6) : oneSet (T i\S) x=oneSet (T i) x := by
      by_cases ht : x∈T i <;> simp [oneSet,hs,ht]
    norm_num only [Fin.sum_univ_five, Fin.reduceSucc, he]
    exact hcount
lemma outside_mass (T S : Set Ω) (hS : MeasurableSet S) (d a : ℝ)
    (hT : μ.real T=2*d) (ha : μ.real (T∩S)=a) : μ.real (T\S)=2*d-a := by
  have h := measureReal_inter_add_sdiff (μ := μ) (s := T) hS
  linarith
end ThirdsFiveIncidence
end JigBundleModule109

/- Inlined module ThirdsCaseBIncidence; original SHA256 f0dbd64464f5e5f5988ae84bf346cb93e4a0ad2e1e0243bad1561b67d3f41b4f -/
section JigBundleModule110
open MeasureTheory
namespace ThirdsCaseBIncidence
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma actual_rows (T : Fin 6 → Set Ω) (S : Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hS : MeasurableSet S) (d : ℝ) (hm : ∀ c, μ.real (T c)=2*d)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=2)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    (μ.real ((T 1\S)∩(T 2\S))+μ.real ((T 1\S)∩(T 3\S))+μ.real ((T 1\S)∩(T 4\S))+μ.real ((T 1\S)∩(T 5\S))=d) ∧
    (μ.real ((T 1\S)∩(T 2\S))+μ.real ((T 2\S)∩(T 3\S))+μ.real ((T 2\S)∩(T 4\S))+μ.real ((T 2\S)∩(T 5\S))=d) ∧
    (μ.real ((T 1\S)∩(T 3\S))+μ.real ((T 2\S)∩(T 3\S))+μ.real ((T 3\S)∩(T 4\S))+μ.real ((T 3\S)∩(T 5\S))=2*d) ∧
    (μ.real ((T 1\S)∩(T 4\S))+μ.real ((T 2\S)∩(T 4\S))+μ.real ((T 3\S)∩(T 4\S))+μ.real ((T 4\S)∩(T 5\S))=2*d) ∧
    (μ.real ((T 1\S)∩(T 5\S))+μ.real ((T 2\S)∩(T 5\S))+μ.real ((T 3\S)∩(T 5\S))+μ.real ((T 4\S)∩(T 5\S))=2*d) := by
  have rows := ThirdsFiveIncidence.five_rows μ (fun i : Fin 5 => T i.succ\S)
    (fun i => (hT i.succ).diff hS) (ThirdsFiveIncidence.outside_count μ T S h0 hc)
  change (μ.real ((T 1\S)∩(T 2\S))+μ.real ((T 1\S)∩(T 3\S))+μ.real ((T 1\S)∩(T 4\S))+μ.real ((T 1\S)∩(T 5\S))=μ.real (T 1\S)) ∧
    (μ.real ((T 1\S)∩(T 2\S))+μ.real ((T 2\S)∩(T 3\S))+μ.real ((T 2\S)∩(T 4\S))+μ.real ((T 2\S)∩(T 5\S))=μ.real (T 2\S)) ∧
    (μ.real ((T 1\S)∩(T 3\S))+μ.real ((T 2\S)∩(T 3\S))+μ.real ((T 3\S)∩(T 4\S))+μ.real ((T 3\S)∩(T 5\S))=μ.real (T 3\S)) ∧
    (μ.real ((T 1\S)∩(T 4\S))+μ.real ((T 2\S)∩(T 4\S))+μ.real ((T 3\S)∩(T 4\S))+μ.real ((T 4\S)∩(T 5\S))=μ.real (T 4\S)) ∧
    (μ.real ((T 1\S)∩(T 5\S))+μ.real ((T 2\S)∩(T 5\S))+μ.real ((T 3\S)∩(T 5\S))+μ.real ((T 4\S)∩(T 5\S))=μ.real (T 5\S)) at rows
  have m1 := ThirdsFiveIncidence.outside_mass μ (T 1) S hS d _ (hm 1) (by simpa [Set.inter_comm] using mb)
  have m2 := ThirdsFiveIncidence.outside_mass μ (T 2) S hS d _ (hm 2) (by simpa [Set.inter_comm] using mc)
  have m3 := ThirdsFiveIncidence.outside_mass μ (T 3) S hS d _ (hm 3) (by simpa [Set.inter_comm] using mD)
  have m4 := ThirdsFiveIncidence.outside_mass μ (T 4) S hS d _ (hm 4) (by simpa [Set.inter_comm] using mE)
  have m5 := ThirdsFiveIncidence.outside_mass μ (T 5) S hS d _ (hm 5) (by simpa [Set.inter_comm] using mF)
  rcases rows with ⟨r1,r2,r3,r4,r5⟩
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
end ThirdsCaseBIncidence
end JigBundleModule110

/- Inlined module ThirdsCaseBMassAssembly; original SHA256 0eb30fd2cf0074971c2bc482e04277ed73ee19fd6f6d74ecd2e859b30b535c60 -/
section JigBundleModule111
open MeasureTheory
namespace ThirdsCaseBMassAssembly
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
def pairMass (T : Fin 6 → Set Ω) (S : Set Ω) (i j : Fin 6) : ℝ := μ.real ((T i∩T j)\S)
lemma nonneg (T : Fin 6 → Set Ω) (S : Set Ω) (i j : Fin 6) : 0≤pairMass μ T S i j := measureReal_nonneg
lemma mass_setup (T : Fin 6 → Set Ω) (S : Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hS : MeasurableSet S) (d : ℝ) (hm : ∀ c, μ.real (T c)=2*d)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=2)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    (pairMass μ T S 1 2+pairMass μ T S 1 3+pairMass μ T S 1 4+pairMass μ T S 1 5=d) ∧
    (pairMass μ T S 1 2+pairMass μ T S 2 3+pairMass μ T S 2 4+pairMass μ T S 2 5=d) ∧
    (pairMass μ T S 1 3+pairMass μ T S 2 3+pairMass μ T S 3 4+pairMass μ T S 3 5=2*d) ∧
    (pairMass μ T S 1 4+pairMass μ T S 2 4+pairMass μ T S 3 4+pairMass μ T S 4 5=2*d) ∧
    (pairMass μ T S 1 5+pairMass μ T S 2 5+pairMass μ T S 3 5+pairMass μ T S 4 5=2*d) := by
  have he (i j : Fin 6) : (T i\S)∩(T j\S)=(T i∩T j)\S := by ext x; simp; tauto
  simpa only [he,pairMass] using ThirdsCaseBIncidence.actual_rows μ T S hT hS d hm h0 hc mb mc mD mE mF
lemma null_pair (T : Fin 6 → Set Ω) (S : Set Ω) (i j : Fin 6) (hn : μ (T i∩T j)=0) :
    pairMass μ T S i j=0 := by
  have hz : μ ((T i∩T j)\S)=0 := measure_mono_null Set.sdiff_subset hn
  simp [pairMass,measureReal_def,hz]
lemma one_mixing_masses (T : Fin 6 → Set Ω) (S : Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hS : MeasurableSet S) (d : ℝ) (hm : ∀ c, μ.real (T c)=2*d)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=2)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0)
    (h15 : μ (T 1∩T 5)=0) (h25 : μ (T 2∩T 5)=0)
    (h35 : pairMass μ T S 3 5≤d) (h45 : pairMass μ T S 4 5≤d) :
    pairMass μ T S 3 4=pairMass μ T S 1 2 ∧ pairMass μ T S 3 5=d ∧ pairMass μ T S 4 5=d ∧
    pairMass μ T S 1 3+pairMass μ T S 2 3=d-pairMass μ T S 1 2 ∧
    pairMass μ T S 1 4+pairMass μ T S 2 4=d-pairMass μ T S 1 2 ∧
    pairMass μ T S 1 3=pairMass μ T S 2 4 ∧ pairMass μ T S 1 4=pairMass μ T S 2 3 := by
  obtain ⟨r1,r2,r3,r4,r5⟩ := mass_setup μ T S hT hS d hm h0 hc mb mc mD mE mF
  exact ThirdsPairMasses.one_mixing_saturated d _ _ _ _ _ _ _ _ _ _
    ⟨nonneg μ T S 1 2,nonneg μ T S 1 3,nonneg μ T S 1 4,nonneg μ T S 1 5,
     nonneg μ T S 2 3,nonneg μ T S 2 4,nonneg μ T S 2 5,nonneg μ T S 3 4,
     nonneg μ T S 3 5,nonneg μ T S 4 5⟩ r1 r2 r3 r4 r5
    (null_pair μ T S 1 5 h15) (null_pair μ T S 2 5 h25) h35 h45
end ThirdsCaseBMassAssembly
end JigBundleModule111

/- Inlined module ThirdsPositiveClass; original SHA256 b5641e9936e5515cdbbaaac98896f7862d185e62ea1eee56dc07d2ed42c444f3 -/
section JigBundleModule112
open MeasureTheory
namespace ThirdsPositiveClass
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma of_not_ae (A : Set Ω) (P : Ω → Prop) (hn : ¬ ∀ᵐ x ∂μ, x∈A → P x) : 0<μ.real A := by
  apply lt_of_le_of_ne measureReal_nonneg
  intro hz
  have hnull : μ A=0 := (measureReal_eq_zero_iff).mp hz.symm
  have he : ∀ᵐ x ∂μ, x∉A := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hnull
  apply hn
  filter_upwards [he] with x hx
  exact fun hh => False.elim (hx hh)
lemma outside_positive (A S T : Set Ω) (hS : MeasurableSet S)
    (hp : 0<μ.real A) (hAT : A⊆T) (hn : μ.real (S∩T)=0) : 0<μ.real (A\S) := by
  have hs : A∩S⊆S∩T := fun x hx => ⟨hx.2,hAT hx.1⟩
  have hm : μ (A∩S)=0 := measure_mono_null hs ((measureReal_eq_zero_iff).mp hn)
  have hr : μ.real (A∩S)=0 := by simp [measureReal_def,hm]
  have he := measureReal_inter_add_sdiff (μ := μ) (s := A) hS
  linarith
end ThirdsPositiveClass
end JigBundleModule112

/- Inlined module ThirdsMixingBounds; original SHA256 a1608c41db4831a23c240f2703d02dc020f7a91fb871cef71f50ee0426f9bed2 -/
section JigBundleModule113
open MeasureTheory
namespace ThirdsMixingBounds
open ThirdsMixingAnchor TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma strict_bounds (f : Ω → ℝ) (hf : Measurable f)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (mf : ∫ x, f x ∂μ=(1:ℝ)/2)
    (X : Set Ω) (hX : MeasurableSet X) (mX : μ.real X=(1:ℝ)/2)
    (hn : ¬ ((f =ᵐ[μ] oneSet X) ∨ (f =ᵐ[μ] (fun x => 1-oneSet X x)))) :
    0 < (∫ x in X, f x ∂μ) ∧ (∫ x in X, f x ∂μ) < (1:ℝ)/2 := by
  have iF := (LowSupportAnalysis.unit_integrable_ae hf bf).restrict (s := X)
  have bb : ∀ᵐ x ∂μ.restrict X, 0 ≤ f x ∧ f x ≤ 1 := ae_restrict_of_ae bf
  have hlo : 0 ≤ ∫ x in X, f x ∂μ := integral_nonneg_of_ae (bb.mono fun _ h => h.1)
  have hhi : (∫ x in X, f x ∂μ) ≤ (1:ℝ)/2 := by
    have hh := integral_mono_ae iF (integrable_const (1:ℝ)) (bb.mono fun _ h => h.2)
    simpa [mX] using hh
  have hn0 : (∫ x in X, f x ∂μ) ≠ 0 := fun h => hn (endpoint_alignment μ f hf bf mf X hX mX (Or.inl h))
  have hn1 : (∫ x in X, f x ∂μ) ≠ (1:ℝ)/2 := fun h => hn (endpoint_alignment μ f hf bf mf X hX mX (Or.inr h))
  exact ⟨lt_of_le_of_ne hlo (Ne.symm hn0),lt_of_le_of_ne hhi hn1⟩
end ThirdsMixingBounds
end JigBundleModule113

/- Inlined module ThirdsMixingSet; original SHA256 b8a7e226ee9ddfcb44cff7204bf5940eed86b5bd72acfc296cb5b010c7d41fc9 -/
section JigBundleModule114
open MeasureTheory
namespace ThirdsMixingSet
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
lemma exists_mixing_set (F : Ω × Ω → ℝ) (hF : Measurable F)
    (T X : Set Ω) (hT : MeasurableSet T) (hX : MeasurableSet X) (mX : ν.real X=(1:ℝ)/2)
    (hb : ∀ᵐ u ∂μ, u∈T → ∀ᵐ x ∂ν, 0 ≤ F (u,x) ∧ F (u,x) ≤ 1)
    (hm : ∀ᵐ u ∂μ, u∈T → (∫ x, F (u,x) ∂ν)=(1:ℝ)/2)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T →
      ((fun x => F (u,x)) =ᵐ[ν] oneSet X) ∨ ((fun x => F (u,x)) =ᵐ[ν] (fun x => 1-oneSet X x)))) :
    ∃ M : Set Ω, MeasurableSet M ∧ μ M ≠ 0 ∧ M⊆T ∧
      (∀ u∈M, 0 < (∫ x in X, F (u,x) ∂ν) ∧ (∫ x in X, F (u,x) ∂ν) < (1:ℝ)/2) := by
  let s := fun u => ∫ x in X, F (u,x) ∂ν
  have hs : Measurable s := by dsimp [s]; fun_prop
  let M := T∩{u | 0 < s u ∧ s u < (1:ℝ)/2}
  have hM : MeasurableSet M := hT.inter ((measurableSet_lt measurable_const hs).inter
    (measurableSet_lt hs measurable_const))
  have hp : μ M ≠ 0 := by
    intro hz
    have hnot : ∀ᵐ u ∂μ, u∉M := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hz
    apply hn
    filter_upwards [hb,hm,hnot] with u bu mu nu
    intro hut
    by_contra hnrow
    have hstrict := ThirdsMixingBounds.strict_bounds ν (fun x => F (u,x))
      (hF.comp (measurable_const.prodMk measurable_id)) (bu hut) (mu hut) X hX mX hnrow
    exact nu ⟨hut,hstrict⟩
  exact ⟨M,hM,hp,Set.inter_subset_left,fun _ h => h.2⟩
end ThirdsMixingSet
end JigBundleModule114

/- Inlined module ThirdsPositiveHalves; original SHA256 99b742ede0b3f746e4022830789be87fa047fa53d1d03966d7b886ff26725671 -/
section JigBundleModule115
open MeasureTheory
namespace ThirdsPositiveHalves
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma pair_positive (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) (bg : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1)
    (mf : ∫ x, f x ∂μ=(1:ℝ)/2) (mg : ∫ x, g x ∂μ=(1:ℝ)/2)
    (hfg : ∀ᵐ x ∂μ, f x+g x=1) (X : Set Ω) (hX : MeasurableSet X) (mX : μ.real X=(1:ℝ)/2)
    (hs : 0 < (∫ x in X, f x ∂μ) ∧ (∫ x in X, f x ∂μ) < (1:ℝ)/2) :
    (0 < ∫ x in X, f x ∂μ) ∧ (0 < ∫ x in X, g x ∂μ) ∧
    (0 < ∫ x in Xᶜ, f x ∂μ) ∧ (0 < ∫ x in Xᶜ, g x ∂μ) := by
  have iF := LowSupportAnalysis.unit_integrable_ae hf bf
  have iG := LowSupportAnalysis.unit_integrable_ae hg bg
  have hx : (∫ x in X, f x ∂μ)+(∫ x in X, g x ∂μ)=(1:ℝ)/2 := by
    rw [← integral_add (f := f) (g := g) (iF.restrict (s := X)) (iG.restrict (s := X))]
    rw [integral_congr_ae (ae_restrict_of_ae hfg)]
    simpa using mX
  have hfc := integral_add_compl hX iF
  have hgc := integral_add_compl hX iG
  rw [mf] at hfc
  rw [mg] at hgc
  exact ⟨hs.1,by linarith,by linarith,by linarith⟩
lemma lift_positive (S X : Set Ω) (hX : MeasurableSet X) (hXS : X⊆S) (f : Ω → ℝ)
    (hp : 0 < ∫ x in X, f x ∂ProbabilityTheory.cond μ S) : 0 < ∫ x in X, f x ∂μ := by
  rw [ThirdsCaseBForced.conditional_set_integral μ S X hX,Set.inter_eq_left.mpr hXS] at hp
  by_contra hn
  have hle : (∫ x in X, f x ∂μ) ≤ 0 := le_of_not_gt hn
  have ha : 0 ≤ (μ.real S)⁻¹ := inv_nonneg.mpr measureReal_nonneg
  have hbad := mul_nonpos_of_nonneg_of_nonpos ha hle
  exact (not_lt_of_ge hbad) hp
end ThirdsPositiveHalves
end JigBundleModule115

/- Inlined module ThirdsActualMixingSet; original SHA256 6d98d99b94c2c59b8186bc87986f4272f4846cfb6c32e2c9334b74260cb6bbc1 -/
section JigBundleModule116
open MeasureTheory
namespace ThirdsActualMixingSet
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma mixing_set (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x)))) :
    ∃ M : Set Ω, MeasurableSet M ∧ μ M ≠ 0 ∧ M⊆T 3∩T 4 ∧
      (∀ᵐ v ∂μ, v∈M →
        (0 < ∫ x in X, W 3 (x,v) ∂μ) ∧ (0 < ∫ x in X, W 4 (v,x) ∂μ) ∧
        (0 < ∫ x in S\X, W 3 (x,v) ∂μ) ∧ (0 < ∫ x in S\X, W 4 (v,x) ∂μ)) := by
  let ν := ProbabilityTheory.cond μ S
  letI : IsProbabilityMeasure ν := ThirdsNormalizedRestriction.conditional_probability μ S d hd mS
  have hac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have mxν : ν.real X=(1:ℝ)/2 := by
    rw [ThirdsNormalizedRestriction.conditional_real μ S X hX,Set.inter_eq_left.mpr hXS,mX,mS]
    field_simp
    <;> nlinarith
  have hRG := rowGood_ae μ W bW sW hpart
  have hact := ae_all_iff.mpr hf
  have hmass : ∀ᵐ u ∂μ, ∀ c, u∈T c → (∫ x, W c (u,x) ∂ν)=(1:ℝ)/2 := by
    filter_upwards [hact] with u hu
    intro c huc
    have hh : act μ (W c) (oneSet S) u=d := by rw [hu c]; simp [oneSet,huc]
    rw [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ (W c) S hS] at hh
    rw [ThirdsNormalizedRestriction.conditional_integral μ S,mS,hh]
    field_simp
    <;> nlinarith
  have hb : ∀ᵐ u ∂μ, u∈T 3∩T 4 → ∀ᵐ x ∂ν, 0 ≤ W 3 (u,x) ∧ W 3 (u,x) ≤ 1 := by
    filter_upwards [hRG] with u hu
    intro _
    exact ((hu.1 3).filter_mono hac.ae_le).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have hm : ∀ᵐ u ∂μ, u∈T 3∩T 4 → (∫ x, W 3 (u,x) ∂ν)=(1:ℝ)/2 := by
    filter_upwards [hmass] with u hu; exact fun h => hu 3 h.1
  obtain ⟨M,hM,pM,subM,strictM⟩ := ThirdsMixingSet.exists_mixing_set μ ν (W 3) (hW 3)
    (T 3∩T 4) X ((hT 3).inter (hT 4)) hX mxν hb hm hn
  refine ⟨M,hM,pM,subM,?_⟩
  filter_upwards [hRG,hact,hmass] with v hgv hav hmv
  intro hvm
  have hv := subM hvm
  have mvi (c : Fin 6) (hc : v∈T c) : act μ (W c) (oneSet S) v=d := by rw [hav c]; simp [oneSet,hc]
  obtain ⟨r,hr,br,mr,er,eg,_⟩ := selected_center μ W hW S hS d hd mS v hgv 3 4 (by decide) (mvi _ hv.1) (mvi _ hv.2)
  have hfg : ∀ᵐ x ∂ν, W 3 (v,x)+W 4 (v,x)=1 := by
    filter_upwards [er,eg] with x hx hy
    change W 3 (v,x)=(1+r x)/2 at hx
    change W 4 (v,x)=(1-r x)/2 at hy
    linarith
  have b3 : ∀ᵐ x ∂ν, 0 ≤ W 3 (v,x) ∧ W 3 (v,x) ≤ 1 := ((hgv.1 3).filter_mono hac.ae_le).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have b4 : ∀ᵐ x ∂ν, 0 ≤ W 4 (v,x) ∧ W 4 (v,x) ≤ 1 := ((hgv.1 4).filter_mono hac.ae_le).mono (fun _ h => ⟨h.1,h.2.1⟩)
  have pp := ThirdsPositiveHalves.pair_positive ν (fun x => W 3 (v,x)) (fun x => W 4 (v,x))
    (by fun_prop) (by fun_prop) b3 b4 (hmv 3 hv.1) (hmv 4 hv.2) hfg X hX mxν (strictM v hvm)
  have eY : (S\X) =ᵐ[ν] Xᶜ := by
    apply ThirdsNormalizedRestriction.conditional_ae μ S hS
    exact Filter.Eventually.of_forall (fun x hxs => by apply propext; change (x∈S ∧ x∉X) ↔ x∉X; simp [hxs])
  have py3 : 0 < ∫ x in S\X, W 3 (v,x) ∂ν := by
    have ee : (∫ x in S\X, W 3 (v,x) ∂ν) = ∫ x in Xᶜ, W 3 (v,x) ∂ν := setIntegral_congr_set eY
    exact ee.symm ▸ pp.2.2.1
  have py4 : 0 < ∫ x in S\X, W 4 (v,x) ∂ν := by
    have ee : (∫ x in S\X, W 4 (v,x) ∂ν) = ∫ x in Xᶜ, W 4 (v,x) ∂ν := setIntegral_congr_set eY
    exact ee.symm ▸ pp.2.2.2
  have px3 := ThirdsPositiveHalves.lift_positive μ S X hX hXS (fun x => W 3 (v,x)) pp.1
  have px4 := ThirdsPositiveHalves.lift_positive μ S X hX hXS (fun x => W 4 (v,x)) pp.2.1
  have py3' := ThirdsPositiveHalves.lift_positive μ S (S\X) (hS.diff hX) Set.sdiff_subset (fun x => W 3 (v,x)) py3
  have py4' := ThirdsPositiveHalves.lift_positive μ S (S\X) (hS.diff hX) Set.sdiff_subset (fun x => W 4 (v,x)) py4
  have esym : (fun x => W 3 (x,v)) =ᵐ[μ] (fun x => W 3 (v,x)) := (hgv.1 3).mono (fun _ h => h.2.2)
  refine ⟨?_,px4,?_,py4'⟩
  · rw [integral_congr_ae (ae_restrict_of_ae esym)]; exact px3
  · rw [integral_congr_ae (ae_restrict_of_ae esym)]; exact py3'
end ThirdsActualMixingSet
end JigBundleModule116

/- Inlined module ThirdsFullTargetRow; original SHA256 5501edf0f12496101abdfff74ea1d3a8129df8b2361bb732a3cb8371cb43189c -/
section JigBundleModule117
open MeasureTheory
namespace ThirdsFullTargetRow
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma extend (f : Ω → ℝ) (hf : Measurable f) (bf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (mf : ∫ x, f x ∂μ=d) (mX : μ.real X=d)
    (he : f =ᵐ[ProbabilityTheory.cond μ S] oneSet X) : f =ᵐ[μ] oneSet X := by
  have hei : ∀ᵐ x ∂μ, x∈S → f x=oneSet X x :=
    (ThirdsInternalProfiles.conditional_ae_iff μ S hS _).mp he
  have hex : f =ᵐ[μ.restrict X] oneSet X := by
    apply (ae_restrict_iff' hX).mpr
    filter_upwards [hei] with x hx
    exact fun hxx => hx (hXS hxx)
  have mi : (∫ x, oneSet X x ∂μ)=d := by simpa [oneSet,integral_indicator hX] using mX
  have mp : (∫ x, f x*oneSet X x ∂μ)=d := by
    rw [ThirdsMixingAnchor.integral_mul_indicator μ f X hX,integral_congr_ae hex]
    simpa [oneSet,integral_indicator hX] using mX
  exact (FourColorEqualRows.equal_indicator_of_saturated_overlap μ f (oneSet X) hf
    (oneSet_measurable X hX) bf (Filter.Eventually.of_forall (oneSet_bounds X)) d mf mi mp).mono (fun _ h => h.1)
end ThirdsFullTargetRow
end JigBundleModule117

/- Inlined module ThirdsCaseBFullRows; original SHA256 96d9e1ebc57a79ae7965a0d1e7083ae96a58ad50f7ffc5c80d9e5d4f0dca3568 -/
section JigBundleModule118
open MeasureTheory
namespace ThirdsCaseBFullRows
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma outside_active_full_other (C : Ω × Ω → ℝ) (hm : Measurable C)
    (hb : ∀ᵐ p ∂μ.prod μ, 0 ≤ C p ∧ C p ≤ 1)
    (hs : ∀ᵐ p ∂μ.prod μ, C p=C (p.2,p.1))
    (S X T : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ᵐ u ∂μ, ∫ x, C (u,x) ∂μ=d)
    (hc : ∀ᵐ p ∂μ.prod μ, p.1∈X → C p=oneSet X p.2)
    (ha : act μ C (oneSet S) =ᵐ[μ] (fun u => d*oneSet T u)) :
    ∀ᵐ u ∂μ, u∉S → u∈T → (fun x => C (u,x)) =ᵐ[μ] oneSet (S\X) := by
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have hcond : (fun x => 1-oneSet X x) =ᵐ[ProbabilityTheory.cond μ S] oneSet (S\X) := by
    apply ThirdsNormalizedRestriction.conditional_ae μ S hS
    exact Filter.Eventually.of_forall (fun x hxs => by by_cases hxx : x∈X <;> simp [oneSet,hxs,hxx])
  have hop := ThirdsCaseBForced.outside_active_opposite μ C hm hb hs S X T hS hX hXS d hd mS mX hc ha
  filter_upwards [hop,Measure.ae_ae_of_ae_prod hb,hr] with u hu bu ru
  intro hus hut
  exact ThirdsFullTargetRow.extend μ (fun x => C (u,x)) (hm.comp (measurable_const.prodMk measurable_id))
    bu S (S\X) hS hY Set.sdiff_subset d ru mY ((hu hus hut).trans hcond)
end ThirdsCaseBFullRows
end JigBundleModule118

/- Inlined module ThirdsActiveZero; original SHA256 a3e9112f6b8fb2e5b59450c85c2a49ec480c556982939864a6f57e025c7ed12b -/
section JigBundleModule119
open MeasureTheory
namespace ThirdsActiveZero
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma join_halves (A F : Ω × Ω → ℝ) (hF : Measurable F)
    (bF : ∀ᵐ p ∂μ.prod μ, 0 ≤ F p ∧ F p ≤ 1)
    (S X Z T : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : d ≠ 0)
    (hf : act μ F (oneSet S) =ᵐ[μ] (fun v => d*oneSet T v))
    (hx : ∀ᵐ z ∂μ, z∈Z → ∀ᵐ v ∂μ, A (z,v)*(∫ y in X, F (v,y) ∂μ)=0)
    (hy : ∀ᵐ z ∂μ, z∈Z → ∀ᵐ v ∂μ, A (z,v)*(∫ y in S\X, F (v,y) ∂μ)=0) :
    ∀ᵐ z ∂μ, z∈Z → ∀ᵐ v ∂μ, v∈T → A (z,v)=0 := by
  have hsum : ∀ᵐ v ∂μ, (∫ y in X, F (v,y) ∂μ)+(∫ y in S\X, F (v,y) ∂μ)=d*oneSet T v := by
    filter_upwards [Measure.ae_ae_of_ae_prod bF,hf] with v bv hv
    have hi := (LowSupportAnalysis.unit_integrable_ae
      (hF.comp (measurable_const.prodMk measurable_id)) bv).restrict (s := S)
    have he := integral_inter_add_sdiff hX hi
    rw [Set.inter_eq_right.mpr hXS] at he
    rw [ThirdsDeterministicTransport.act_oneSet_eq_setIntegral μ F S hS] at hv
    exact he.trans hv
  filter_upwards [hx,hy] with z hzx hzy
  intro hzz
  filter_upwards [hzx hzz,hzy hzz,hsum] with v hvx hvy hvsum
  intro hvt
  have hh : (∫ y in X, F (v,y) ∂μ)+(∫ y in S\X, F (v,y) ∂μ)=d := by simpa [oneSet,hvt] using hvsum
  have hp : A (z,v)*d=0 := by rw [← hh,mul_add,hvx,hvy]; ring
  exact (mul_eq_zero.mp hp).resolve_right hd
end ThirdsActiveZero
end JigBundleModule119

/- Inlined module ThirdsCaseBFiveZero; original SHA256 f3740bb503717db2a65b954e3069baa04d3709f95af2b91145422be1fb1fb004 -/
section JigBundleModule120
open MeasureTheory
namespace ThirdsCaseBFiveZero
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma mixing_forces_zero (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x)))) :
    ∀ᵐ z ∂μ, z∈T 1∩T 2 → ∀ᵐ v ∂μ, v∈T 5 → W 0 (z,v)=0 := by
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have hXX : S\(S\X)=X := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hs,hn⟩; by_contra hx; exact hn ⟨hs,hx⟩
    · intro hx; exact ⟨hXS hx,fun h => h.2 hx⟩
  obtain ⟨M,hM,pM,subM,hanchor⟩ := ThirdsActualMixingSet.mixing_set μ W hW bW sW hpart
    S X hS hX hXS d hd mS mX T hT hf hn
  have hout : ∀ᵐ z ∂μ, z∈T 1∩T 2 → z∉S := by
    filter_upwards [h0,hc] with z hz0 hzc
    intro hz hzs
    have h1 : oneSet (T 1) z=1 := by simp [oneSet,hz.1]
    have h2 : oneSet (T 2) z=1 := by simp [oneSet,hz.2]
    have hh0 : oneSet (T 0) z=1 := by rw [hz0]; simp [oneSet,hzs]
    simp only [Fin.sum_univ_six] at hzc
    nlinarith [(oneSet_bounds (T 3) z).1,(oneSet_bounds (T 4) z).1,(oneSet_bounds (T 5) z).1]
  have hbr := ThirdsCaseBFullRows.outside_active_full_other μ (W 1) (hW 1) (bW 1) (sW 1)
    S X (T 1) hS hX hXS d hd mS mX (hr 1) hcl1 (hf 1)
  have hcr := ThirdsCaseBFullRows.outside_active_full_other μ (W 2) (hW 2) (bW 2) (sW 2)
    S (S\X) (T 2) hS hY Set.sdiff_subset d hd mS mY (hr 2) hcl2 (hf 2)
  have hrootX : ∀ᵐ z ∂μ, z∈T 1∩T 2 → (fun x => W 2 (z,x)) =ᵐ[μ] oneSet X := by
    filter_upwards [hout,hcr] with z ho hh
    intro hz
    simpa only [hXX] using hh (ho hz) hz.2
  have hrootY : ∀ᵐ z ∂μ, z∈T 1∩T 2 → (fun x => W 1 (z,x)) =ᵐ[μ] oneSet (S\X) := by
    filter_upwards [hout,hbr] with z ho hh
    intro hz; exact hh (ho hz) hz.1
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![5,1,3,4,2,0] (by decide)
  let τ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![5,2,3,4,1,0] (by decide)
  have part (ρ : Equiv.Perm (Fin 6)) : ∀ᵐ p ∂μ.prod μ, ∑ c, W (ρ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp ρ (fun c => W c p)]; exact hp
  have ax : ∀ᵐ v ∂μ, v∈M → (0 < ∫ x in X, W 3 (x,v) ∂μ) ∧ (0 < ∫ x in X, W 4 (v,x) ∂μ) := by
    filter_upwards [hanchor] with v hv; intro hm; exact ⟨(hv hm).1,(hv hm).2.1⟩
  have ay : ∀ᵐ v ∂μ, v∈M → (0 < ∫ x in S\X, W 3 (x,v) ∂μ) ∧ (0 < ∫ x in S\X, W 4 (v,x) ∂μ) := by
    filter_upwards [hanchor] with v hv; intro hm; exact (hv hm).2.2
  have zx := ThirdsActualFivePath.exclusion μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) (part σ) X (T 1∩T 2) M hX pM hcl1 hrootX ax (hz σ)
  have zy := ThirdsActualFivePath.exclusion μ (fun c => W (τ c)) (fun c => hW (τ c))
    (fun c => bW (τ c)) (fun c => sW (τ c)) (part τ) (S\X) (T 1∩T 2) M hY pM hcl2 hrootY ay (hz τ)
  exact ThirdsActiveZero.join_halves μ (W 0) (W 5) (hW 5) (bW 5) S X (T 1∩T 2) (T 5)
    hS hX hXS d (ne_of_gt hd) (hf 5) zx zy
end ThirdsCaseBFiveZero
end JigBundleModule120

/- Inlined module ThirdsCaseBVariablePairs; original SHA256 2f92a7433149a74d0b247db3b3becffd18ab32b2daaecef51f7121dc15659857 -/
section JigBundleModule121
open MeasureTheory
namespace ThirdsCaseBVariablePairs
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma variable_pair (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (σ : Equiv.Perm (Fin 6)) (s0 : σ 0=0) (s1 : σ 1=1) (s2 : σ 2=2)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T (σ 3)∩T (σ 4) →
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x)))) :
    μ (T 1∩T (σ 5))=0 ∧ μ (T 2∩T (σ 5))=0 ∧
    ∀ᵐ z ∂μ, z∈T 1∩T 2 → ∀ᵐ v ∂μ, v∈T (σ 5) → W 0 (z,v)=0 := by
  obtain ⟨e0,e1,e2⟩ := ThirdsCaseBLayout.six_forms μ W hW bW sW hpart S X hS hX hXS hcl1 hcl2 haX haY
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have count : ∀ᵐ u ∂μ, ∑ c, oneSet (T (σ c)) u=2 := by
    filter_upwards [hc] with u hu
    rw [Equiv.sum_comp σ (fun c => oneSet (T c) u)]; exact hu
  have cycles : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have nulls := ThirdsCaseBPeripheral.both_null μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) part S X hS hX hXS d hd mS mX
    (fun c => T (σ c)) (fun c => hf (σ c)) (by simpa only [s0] using h0) count
    (by simpa only [s1] using hcl1) (by simpa only [s2] using hcl2)
    (by simpa only [s1] using e1) (by simpa only [s0] using e0) (by simpa only [s2] using e2) cycles hn
  have zero := ThirdsCaseBFiveZero.mixing_forces_zero μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) part S X hS hX hXS d hd mS mX
    (fun c => hr (σ c)) (fun c => T (σ c)) (fun c => hT (σ c)) (fun c => hf (σ c))
    (by simpa only [s0] using h0) count (by simpa only [s1] using hcl1)
    (by simpa only [s2] using hcl2) cycles hn
  simpa only [s0,s1,s2] using And.intro nulls.1 (And.intro nulls.2 zero)
end ThirdsCaseBVariablePairs
end JigBundleModule121

/- Inlined module ThirdsCaseBActualMasses; original SHA256 99f0d3fa1a9dfeca37de1fb52d2735bc44e44a38a1a89dd2825242ab33b1b567 -/
section JigBundleModule122
open MeasureTheory
namespace ThirdsCaseBActualMasses
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma mixing_mass_structure (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    0<pairMass μ T S 1 2 ∧ pairMass μ T S 3 4=pairMass μ T S 1 2 ∧
    pairMass μ T S 3 5=d ∧ pairMass μ T S 4 5=d ∧
    μ (T 1∩T 5)=0 ∧ μ (T 2∩T 5)=0 ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 5)\S → W 4 p=1) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 4∩T 5)\S → W 3 p=1) := by
  obtain ⟨n15,n25,hzero⟩ := ThirdsCaseBVariablePairs.variable_pair μ W hW bW sW hpart
    S X hS hX hXS d hd mS mX hr T hT hf h0 hc hcl1 hcl2 haX haY hz
    (Equiv.refl _) rfl rfl rfl hn
  have hp : 0<μ.real (T 3∩T 4) := ThirdsPositiveClass.of_not_ae μ _ _ hn
  have hp' : 0<pairMass μ T S 3 4 :=
    ThirdsPositiveClass.outside_positive μ (T 3∩T 4) S (T 3) hS hp Set.inter_subset_left mD
  obtain ⟨r1,r2,r3,r4,r5⟩ := mass_setup μ T S hT hS d hm h0 hc mb mc mD mE mF
  have hh := ThirdsPairMasses.one_mixing d _ _ _ _ _ _ _ _ _ _
    ⟨nonneg μ T S 1 2,nonneg μ T S 1 3,nonneg μ T S 1 4,nonneg μ T S 1 5,
     nonneg μ T S 2 3,nonneg μ T S 2 4,nonneg μ T S 2 5,nonneg μ T S 3 4,
     nonneg μ T S 3 5,nonneg μ T S 4 5⟩ r1 r2 r3 r4 r5
    (null_pair μ T S 1 5 n15) (null_pair μ T S 2 5 n25)
  have pZ : 0<pairMass μ T S 1 2 := by rw [← hh.1]; exact hp'
  have hb := ThirdsCaseBForced.forced_mass_bounds μ W hW bW sW hpart d (ne_of_gt hd) hr
    S hS T hT hf hzero pZ
  have hmasses := one_mixing_masses μ T S hT hS d hm h0 hc mb mc mD mE mF n15 n25 hb.1 hb.2
  have rects := ThirdsCaseBForced.forced_rectangles μ W hW bW sW hpart d (ne_of_gt hd) hr S hS T hT hf hzero
  exact ⟨pZ,hmasses.1,hmasses.2.1,hmasses.2.2.1,n15,n25,rects.1,rects.2⟩
end ThirdsCaseBActualMasses
end JigBundleModule122

/- Inlined module ThirdsSixthTarget; original SHA256 096caa813f2cf8e67126c179a54924b1adab4a18eb5e72ef6842e30476576bac -/
section JigBundleModule123
open MeasureTheory
namespace ThirdsSixthTarget
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma binary_remainder (v : Fin 5 → ℝ) (hv : ∀ i, v i=0 ∨ v i=1) (hle : ∑ i, v i≤1) :
    1-(∑ i, v i) = if (∑ i, v i)=0 then 1 else 0 := by
  rcases hv 0 with h0|h0 <;> rcases hv 1 with h1|h1 <;> rcases hv 2 with h2|h2 <;>
    rcases hv 3 with h3|h3 <;> rcases hv 4 with h4|h4 <;>
    simp only [Fin.sum_univ_five,h0,h1,h2,h3,h4] at hle ⊢ <;> norm_num at *
lemma full_mass (C : Ω × Ω → ℝ) (d : ℝ)
    (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (Z T : Set Ω) (hT : MeasurableSet T) (hp : 0<μ.real Z)
    (hf : ∀ᵐ p ∂μ.prod μ, p.1∈Z → C p=oneSet T p.2) : μ.real T=d := by
  have hh : ∀ᵐ x ∂μ, x∈Z → μ.real T=d := by
    filter_upwards [hr,Measure.ae_ae_of_ae_prod hf] with x hx hf
    intro hz
    have he : (fun y => C (x,y)) =ᵐ[μ] oneSet T := hf.mono fun y hy => hy hz
    simpa [integral_congr_ae he,oneSet,integral_indicator hT] using hx
  have hn : μ Z≠0 := by
    intro hn
    have he : μ.real Z=0 := by simp [measureReal_def,hn]
    linarith
  obtain ⟨x,hx,hhx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn (ae_restrict_of_ae hh)
  exact hhx hx
lemma sixth_target (W : Fin 6 → Ω × Ω → ℝ)
    (b5 : ∀ᵐ p ∂μ.prod μ, 0≤W 5 p)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, W 5 (x,y) ∂μ=d)
    (Z : Set Ω) (hp : 0<μ.real Z)
    (G : Fin 5 → Set Ω) (hG : ∀ i, MeasurableSet (G i))
    (hf : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈Z → W i.castSucc p=oneSet (G i) p.2) :
    ∃ R : Set Ω, MeasurableSet R ∧ μ.real R=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈Z → W 5 p=oneSet R p.2) := by
  classical
  let R : Set Ω := {y | (∑ i, oneSet (G i) y)=0}
  have hR : MeasurableSet R := measurableSet_eq_fun
    (Finset.measurable_sum _ (fun i _ => oneSet_measurable (G i) (hG i))) measurable_const
  have hfull : ∀ᵐ p ∂μ.prod μ, p.1∈Z → W 5 p=oneSet R p.2 := by
    have hall := ae_all_iff.mpr hf
    filter_upwards [b5,hpart,hall] with p hp5 hpsum hpf
    intro hz
    have hs : (∑ i : Fin 5, oneSet (G i) p.2)+W 5 p=1 := by
      rw [Fin.sum_univ_castSucc] at hpsum
      change (∑ i : Fin 5, W i.castSucc p)+W 5 p=1 at hpsum
      simpa only [funext (fun i => hpf i hz)] using hpsum
    have hle : (∑ i : Fin 5, oneSet (G i) p.2)≤1 := by linarith
    have he := binary_remainder (fun i => oneSet (G i) p.2) (fun i => oneSet_binary (G i) p.2) hle
    have hw : W 5 p=1-(∑ i : Fin 5, oneSet (G i) p.2) := by linarith
    rw [hw,he]
    change (if p.2∈R then (1:ℝ) else 0)=oneSet R p.2
    by_cases hh : p.2∈R
    · rw [if_pos hh]; exact (Set.indicator_of_mem hh (fun _ => (1:ℝ))).symm
    · rw [if_neg hh]; exact (Set.indicator_of_notMem hh (fun _ => (1:ℝ))).symm
  exact ⟨R,hR,full_mass μ (W 5) d hr Z R hR hp hfull,hfull⟩
end ThirdsSixthTarget
end JigBundleModule123

/- Inlined module ThirdsFullRectangle; original SHA256 c3dd18c8af904650b9f91f83b3fe1db66fd62cd11c68c4c24d7f5db02c93e9fe -/
section JigBundleModule124
open MeasureTheory
namespace ThirdsFullRectangle
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma full_rows (C : Ω×Ω → ℝ) (hC : Measurable C)
    (bC : ∀ᵐ p ∂μ.prod μ, 0≤C p ∧ C p≤1)
    (d : ℝ) (hr : ∀ᵐ x ∂μ, ∫ y, C (x,y) ∂μ=d)
    (I T : Set Ω) (hI : MeasurableSet I) (hT : MeasurableSet T) (mT : μ.real T=d)
    (hfull : ∀ᵐ p ∂μ.prod μ, p.1∈I → p.2∈T → C p=1) :
    ∀ᵐ p ∂μ.prod μ, p.1∈I → C p=oneSet T p.2 := by
  apply (Measure.ae_prod_iff_ae_ae ((hI.preimage measurable_fst).imp
    (measurableSet_eq_fun hC ((oneSet_measurable T hT).comp measurable_snd)))).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod bC,Measure.ae_ae_of_ae_prod hfull,hr] with x bx fx rx
  by_cases hx : x∈I
  · have he : (fun y => C (x,y)) =ᵐ[ProbabilityTheory.cond μ T] oneSet T := by
      apply ThirdsNormalizedRestriction.conditional_ae μ T hT
      filter_upwards [fx] with y hy
      intro hyt
      simpa [oneSet,hyt] using hy hx hyt
    exact (ThirdsFullTargetRow.extend μ (fun y => C (x,y)) (by fun_prop) bx T T hT hT
      Set.Subset.rfl d rx mT he).mono (fun _ h _ => h)
  · exact Filter.Eventually.of_forall (fun _ h => (hx h).elim)
end ThirdsFullRectangle
end JigBundleModule124

/- Inlined module ThirdsCaseBTwoMixing; original SHA256 126b96c735b2fb550fc134f7f43c1120b8ce50829dc933a6d54ba4be3e0f1575 -/
section JigBundleModule125
open MeasureTheory
namespace ThirdsCaseBTwoMixing
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma two_mixing_structure (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hn35 : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 5 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    pairMass μ T S 1 2=d ∧ pairMass μ T S 3 4=d ∧ pairMass μ T S 3 5=d ∧ pairMass μ T S 4 5=d ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 5)\S → W 4 p=1) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 4∩T 5)\S → W 3 p=1) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 4)\S → W 5 p=1) := by
  have h := ThirdsCaseBActualMasses.mixing_mass_structure μ W hW bW sW hpart S X hS hX hXS
    d hd mS mX hr T hT hf h0 hc hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,1,2,3,5,4] (by decide)
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have count : ∀ᵐ u ∂μ, ∑ c, oneSet (T (σ c)) u=2 := by
    filter_upwards [hc] with u hu
    rw [Equiv.sum_comp σ (fun c => oneSet (T c) u)]; exact hu
  have cycles : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have k := ThirdsCaseBActualMasses.mixing_mass_structure μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) part S X hS hX hXS d hd mS mX
    (fun c => hr (σ c)) (fun c => T (σ c)) (fun c => hT (σ c)) (fun c => hf (σ c))
    h0 count hcl1 hcl2 haX haY cycles hn35 (fun c => hm (σ c)) mb mc mD mF mE
  have hzMass : pairMass μ T S 1 2=d := k.2.1.symm.trans h.2.2.1
  exact ⟨hzMass,h.2.1.trans hzMass,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2,k.2.2.2.2.2.2.1⟩
lemma five_targets (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hn35 : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 5 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, c≠0 → ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
  obtain ⟨mZ,mH,mI,mJ,r4,r3,r5⟩ := two_mixing_structure μ W hW bW sW hpart S X hS hX hXS
    d hd mS mX hr T hT hf h0 hc hcl1 hcl2 haX haY hz hn hn35 hm mb mc mD mE mF
  have hZ : MeasurableSet ((T 1∩T 2)\S) := ((hT 1).inter (hT 2)).diff hS
  have hH : MeasurableSet ((T 3∩T 4)\S) := ((hT 3).inter (hT 4)).diff hS
  have hI : MeasurableSet ((T 3∩T 5)\S) := ((hT 3).inter (hT 5)).diff hS
  have hJ : MeasurableSet ((T 4∩T 5)\S) := ((hT 4).inter (hT 5)).diff hS
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have hXX : S\(S\X)=X := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hs,hn⟩; by_contra hx; exact hn ⟨hs,hx⟩
    · intro hx; exact ⟨hXS hx,fun h => h.2 hx⟩
  have rb := ThirdsCaseBFullRows.outside_active_full_other μ (W 1) (hW 1) (bW 1) (sW 1)
    S X (T 1) hS hX hXS d hd mS mX (hr 1) hcl1 (hf 1)
  have rc := ThirdsCaseBFullRows.outside_active_full_other μ (W 2) (hW 2) (bW 2) (sW 2)
    S (S\X) (T 2) hS hY Set.sdiff_subset d hd mS mY (hr 2) hcl2 (hf 2)
  have fb : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 1 p=oneSet (S\X) p.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((hZ.preimage measurable_fst).imp
      (measurableSet_eq_fun (hW 1) ((oneSet_measurable (S\X) hY).comp measurable_snd)))).mpr
    filter_upwards [rb] with x hx
    by_cases h : x∈(T 1∩T 2)\S
    · exact (hx h.2 h.1.1).mono (fun _ he _ => he)
    · exact Filter.Eventually.of_forall (fun _ hh => (h hh).elim)
  have fc : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 2 p=oneSet X p.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((hZ.preimage measurable_fst).imp
      (measurableSet_eq_fun (hW 2) ((oneSet_measurable X hX).comp measurable_snd)))).mpr
    filter_upwards [rc] with x hx
    by_cases h : x∈(T 1∩T 2)\S
    · have hh := hx h.2 h.1.2
      rw [hXX] at hh
      exact hh.mono (fun _ he _ => he)
    · exact Filter.Eventually.of_forall (fun _ hh => (h hh).elim)
  have f3 := ThirdsFullRectangle.full_rows μ (W 3) (hW 3) (bW 3) d (hr 3)
    ((T 1∩T 2)\S) ((T 4∩T 5)\S) hZ hJ mJ r3
  have f4 := ThirdsFullRectangle.full_rows μ (W 4) (hW 4) (bW 4) d (hr 4)
    ((T 1∩T 2)\S) ((T 3∩T 5)\S) hZ hI mI r4
  have f5 := ThirdsFullRectangle.full_rows μ (W 5) (hW 5) (bW 5) d (hr 5)
    ((T 1∩T 2)\S) ((T 3∩T 4)\S) hZ hH mH r5
  refine ⟨mZ,?_⟩
  intro c hc0
  fin_cases c
  · exact (hc0 rfl).elim
  · exact ⟨S\X,hY,mY,fb⟩
  · exact ⟨X,hX,mX,fc⟩
  · exact ⟨(T 4∩T 5)\S,hJ,mJ,f3⟩
  · exact ⟨(T 3∩T 5)\S,hI,mI,f4⟩
  · exact ⟨(T 3∩T 4)\S,hH,mH,f5⟩
lemma two_mixing_twin (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hn35 : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 5 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
  classical
  obtain ⟨mZ,htargets⟩ := five_targets μ W hW bW sW hpart S X hS hX hXS
    d hd mS mX hr T hT hf h0 hc hcl1 hcl2 haX haY hz hn hn35 hm mb mc mD mE mF
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![1,2,3,4,5,0] (by decide)
  have hne (i : Fin 5) : σ i.castSucc≠0 := by fin_cases i <;> decide
  choose G hG mG fG using (fun i : Fin 5 => htargets (σ i.castSucc) (hne i))
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have pZ : 0<μ.real ((T 1∩T 2)\S) := by change 0<pairMass μ T S 1 2; rw [mZ]; exact hd
  obtain ⟨R,hR,mR,fR⟩ := ThirdsSixthTarget.sixth_target μ (fun c => W (σ c))
    ((bW 0).mono fun _ h => h.1) part d (hr 0) ((T 1∩T 2)\S) pZ G hG fG
  refine ⟨mZ,?_⟩
  intro c
  by_cases hc0 : c=0
  · subst c; exact ⟨R,hR,mR,fR⟩
  · exact htargets c hc0
end ThirdsCaseBTwoMixing

end JigBundleModule125

/- Inlined module ThirdsOneMixingFourTargets; original SHA256 bf7cfbe111f0a72e3fed1221c9d55c885afacdc1fc205cb8efb90359eb8ccb21 -/
section JigBundleModule126
open MeasureTheory
namespace ThirdsOneMixingFourTargets
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma four_targets (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    0<pairMass μ T S 1 2 ∧ pairMass μ T S 3 4=pairMass μ T S 1 2 ∧
    pairMass μ T S 3 5=d ∧ pairMass μ T S 4 5=d ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 1 p=oneSet (S\X) p.2) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 2 p=oneSet X p.2) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 3 p=oneSet ((T 4∩T 5)\S) p.2) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 4 p=oneSet ((T 3∩T 5)\S) p.2) := by
  obtain ⟨pZ,mH,mI,mJ,n15,n25,r4,r3⟩ := ThirdsCaseBActualMasses.mixing_mass_structure
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  have hZ : MeasurableSet ((T 1∩T 2)\S) := ((hT 1).inter (hT 2)).diff hS
  have hH : MeasurableSet ((T 3∩T 4)\S) := ((hT 3).inter (hT 4)).diff hS
  have hI : MeasurableSet ((T 3∩T 5)\S) := ((hT 3).inter (hT 5)).diff hS
  have hJ : MeasurableSet ((T 4∩T 5)\S) := ((hT 4).inter (hT 5)).diff hS
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have hXX : S\(S\X)=X := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hs,hn⟩; by_contra hx; exact hn ⟨hs,hx⟩
    · intro hx; exact ⟨hXS hx,fun h => h.2 hx⟩
  have rb := ThirdsCaseBFullRows.outside_active_full_other μ (W 1) (hW 1) (bW 1) (sW 1)
    S X (T 1) hS hX hXS d hd mS mX (hr 1) hcl1 (hf 1)
  have rc := ThirdsCaseBFullRows.outside_active_full_other μ (W 2) (hW 2) (bW 2) (sW 2)
    S (S\X) (T 2) hS hY Set.sdiff_subset d hd mS mY (hr 2) hcl2 (hf 2)
  have fb : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 1 p=oneSet (S\X) p.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((hZ.preimage measurable_fst).imp
      (measurableSet_eq_fun (hW 1) ((oneSet_measurable (S\X) hY).comp measurable_snd)))).mpr
    filter_upwards [rb] with x hx
    by_cases h : x∈(T 1∩T 2)\S
    · exact (hx h.2 h.1.1).mono (fun _ he _ => he)
    · exact Filter.Eventually.of_forall (fun _ hh => (h hh).elim)
  have fc : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 2 p=oneSet X p.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((hZ.preimage measurable_fst).imp
      (measurableSet_eq_fun (hW 2) ((oneSet_measurable X hX).comp measurable_snd)))).mpr
    filter_upwards [rc] with x hx
    by_cases h : x∈(T 1∩T 2)\S
    · have hh := hx h.2 h.1.2
      rw [hXX] at hh
      exact hh.mono (fun _ he _ => he)
    · exact Filter.Eventually.of_forall (fun _ hh => (h hh).elim)
  have f3 := ThirdsFullRectangle.full_rows μ (W 3) (hW 3) (bW 3) d (hr 3)
    ((T 1∩T 2)\S) ((T 4∩T 5)\S) hZ hJ mJ r3
  have f4 := ThirdsFullRectangle.full_rows μ (W 4) (hW 4) (bW 4) d (hr 4)
    ((T 1∩T 2)\S) ((T 3∩T 5)\S) hZ hI mI r4
  exact ⟨pZ,mH,mI,mJ,fb,fc,f3,f4⟩
end ThirdsOneMixingFourTargets
end JigBundleModule126

/- Inlined module ThirdsCaseBNoMixing; original SHA256 a748c89b40d008c7d74673e447a2bfb13fd346eab03ea513b364c162afd042c3 -/
section JigBundleModule127
open MeasureTheory
namespace ThirdsCaseBNoMixing
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
def Aligned (ν : Measure Ω) (f : Ω → ℝ) (X : Set Ω) : Prop :=
  (f =ᵐ[ν] oneSet X) ∨ (f =ᵐ[ν] (fun x => 1-oneSet X x))
lemma aligned_complement (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (S X : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d)
    (u : Ω) (hu : RowGood μ W u) (i j : Fin 6) (hij : i≠j)
    (mi : act μ (W i) (oneSet S) u=d) (mj : act μ (W j) (oneSet S) u=d)
    (ha : Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X) :
    Aligned (ProbabilityTheory.cond μ S) (fun x => W j (u,x)) X := by
  obtain ⟨r,hr,br,mr,ei,ej,hbridge⟩ := selected_center μ W hW S hS d hd mS u hu i j hij mi mj
  rcases ha with ha | ha
  · right
    filter_upwards [ha,ei,ej] with x hx hi hj
    linarith
  · left
    filter_upwards [ha,ei,ej] with x hx hi hj
    linarith
lemma endpoint (f : Ω → ℝ) (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X)
    (hXS : X⊆S) (d : ℝ) (mX : μ.real X=d)
    (hp : (f =ᵐ[ProbabilityTheory.cond μ S] (fun _ => 0)) ∨ Aligned (ProbabilityTheory.cond μ S) f X) :
    (∫ x in X, f x ∂μ)=0 ∨ (∫ x in X, f x ∂μ)=d := by
  have convert (a : ℝ) (ha : ∀ᵐ x ∂ProbabilityTheory.cond μ S, x∈X → f x=a) :
      (∫ x in X, f x ∂μ)=a*d := by
    have hb := (ThirdsInternalProfiles.conditional_ae_iff μ S hS _).mp ha
    have he : ∀ᵐ x ∂μ.restrict X, f x=a := by
      apply (ae_restrict_iff' hX).mpr
      filter_upwards [hb] with x hx
      intro hxx; exact hx (hXS hxx) hxx
    rw [integral_congr_ae he]
    simp [mX,mul_comm]
  rcases hp with hz | hp | hp
  · left
    simpa using convert 0 (hz.mono fun x hx _ => hx)
  · right
    apply (convert 1 ?_).trans (by ring)
    filter_upwards [hp] with x hx
    intro hxx; simpa [oneSet,hxx] using hx
  · left
    apply (convert 0 ?_).trans (by ring)
    filter_upwards [hp] with x hx
    intro hxx; simpa [oneSet,hxx] using hx
lemma active_partner (t : Fin 6 → ℝ) (hb : ∀ i, t i=0 ∨ t i=1)
    (hs : ∑ i, t i=2) (i : Fin 6) (hi : t i=1) : ∃ j, j≠i ∧ t j=1 := by
  classical
  by_contra hn
  push_neg at hn
  have hz : ∀ j, j≠i → t j=0 := by
    intro j hji
    rcases hb j with h | h
    · exact h
    · exact (hn j hji h).elim
  have he : (∑ j, t j)=t i := Finset.sum_eq_single i
    (fun j _ hji => hz j hji) (fun h => (h (Finset.mem_univ i)).elim)
  linarith

lemma outside_profiles (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hb : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hg : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (hn : ∀ᵐ u ∂μ, ∀ i j : Fin 6, 3 ≤ i.val → 3 ≤ j.val → i≠j →
      u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X) :
    ∀ᵐ u ∂μ, u∉S → ∀ c,
      ((fun x => W c (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun _ => 0)) ∨
      Aligned (ProbabilityTheory.cond μ S) (fun x => W c (u,x)) X := by
  let ν := ProbabilityTheory.cond μ S
  have hac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have hXX : S\(S\X)=X := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hs,hn⟩; by_contra hx; exact hn ⟨hs,hx⟩
    · intro hx; exact ⟨hXS hx,fun h => h.2 hx⟩
  have ey : oneSet (S\X) =ᵐ[ν] (fun x => 1-oneSet X x) := by
    apply ThirdsNormalizedRestriction.conditional_ae μ S hS
    exact Filter.Eventually.of_forall (fun x hx => by by_cases hxx : x∈X <;> simp [oneSet,hx,hxx])
  have hbr := ThirdsCaseBFullRows.outside_active_full_other μ (W 1) (hW 1) (bW 1) (sW 1)
    S X (T 1) hS hX hXS d hd mS mX (hr 1) hb (hf 1)
  have hgr := ThirdsCaseBFullRows.outside_active_full_other μ (W 2) (hW 2) (bW 2) (sW 2)
    S (S\X) (T 2) hS hY Set.sdiff_subset d hd mS mY (hr 2) hg (hf 2)
  filter_upwards [rowGood_ae μ W bW sW hpart,ae_all_iff.mpr hf,h0,hc,hbr,hgr,hn] with u hu hfu hu0 hcu hbu hgu hnu
  intro hus c
  by_cases hct : u∈T c
  · right
    have mass (i : Fin 6) (hi : u∈T i) : act μ (W i) (oneSet S) u=d := by
      rw [hfu i]; simp [oneSet,hi]
    have nt0 : u∉T 0 := by
      intro ht; simp [oneSet,ht,hus] at hu0
    have a1 (ht : u∈T 1) : Aligned ν (fun x => W 1 (u,x)) X :=
      Or.inr (((hbu hus ht).filter_mono hac.ae_le).trans ey)
    have a2 (ht : u∈T 2) : Aligned ν (fun x => W 2 (u,x)) X := by
      left
      simpa only [hXX] using (hgu hus ht).filter_mono hac.ae_le
    by_cases c1 : c=1
    · subst c; exact a1 hct
    by_cases c2 : c=2
    · subst c; exact a2 hct
    have c0 : c≠0 := fun h => nt0 (h ▸ hct)
    have cv : 3 ≤ c.val := by omega
    obtain ⟨j,hjc,hjt⟩ := active_partner (fun i => oneSet (T i) u)
      (fun i => oneSet_binary (T i) u) hcu c (by simp [oneSet,hct])
    have htj : u∈T j := by by_contra h; simp [oneSet,h] at hjt
    by_cases j1 : j=1
    · subst j
      exact aligned_complement μ W hW S X hS d hd mS u hu 1 c hjc (mass 1 htj) (mass c hct) (a1 htj)
    by_cases j2 : j=2
    · subst j
      exact aligned_complement μ W hW S X hS d hd mS u hu 2 c hjc (mass 2 htj) (mass c hct) (a2 htj)
    have j0 : j≠0 := fun h => nt0 (h ▸ htj)
    exact hnu c j cv (by omega) (Ne.symm hjc) ⟨hct,htj⟩
  · left
    apply ThirdsOutsideProfiles.inactive_zero μ W hW S hS d hd mS u hu c
    rw [hfu c]; simp [oneSet,hct]

lemma inside_endpoints (W : Fin 6 → Ω×Ω → ℝ)
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hX : MeasurableSet X) (d : ℝ) (mX : μ.real X=d)
    (hb : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2) :
    ∀ᵐ u ∂μ, u∈S → ∀ c, (∫ x in X, W c (u,x) ∂μ)=0 ∨ (∫ x in X, W c (u,x) ∂μ)=d := by
  filter_upwards [Measure.ae_ae_of_ae_prod (ae_all_iff.mpr bW),Measure.ae_ae_of_ae_prod hpart,
    Measure.ae_ae_of_ae_prod hb,Measure.ae_ae_of_ae_prod haY] with u bu pu hbu hau
  intro hus c
  have exists_full : ∃ j : Fin 6, ∀ᵐ x ∂μ, x∈X → W j (u,x)=1 := by
    by_cases hux : u∈X
    · refine ⟨1,?_⟩
      filter_upwards [hbu] with x hx
      intro hxx; simpa [oneSet,hxx] using hx hux
    · refine ⟨0,?_⟩
      filter_upwards [hau] with x hx
      intro hxx; simpa [oneSet,hxx] using hx ⟨hus,hux⟩
  obtain ⟨j,hj⟩ := exists_full
  by_cases hcj : c=j
  · right
    subst c
    have he : ∀ᵐ x ∂μ.restrict X, W j (u,x)=1 := (ae_restrict_iff' hX).mpr hj
    rw [integral_congr_ae he]
    simp [mX]
  · left
    have he : ∀ᵐ x ∂μ.restrict X, W c (u,x)=0 := by
      apply (ae_restrict_iff' hX).mpr
      filter_upwards [bu,pu,hj] with x bx px jx
      intro hxx
      have hsum : (∑ i ∈ ({c,j} : Finset (Fin 6)), W i (u,x)) ≤ ∑ i, W i (u,x) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => (bx i).1)
      rw [Finset.sum_pair hcj,px,jx hxx] at hsum
      linarith [(bx c).1]
    rw [integral_congr_ae he]
    simp
lemma no_mixing_twin (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hb : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hg : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hn : ∀ᵐ u ∂μ, ∀ i j : Fin 6, 3 ≤ i.val → 3 ≤ j.val → i≠j →
      u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X) :
    ∀ c, ∃ U : Set Ω, MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈X → W c p=oneSet U p.2) := by
  have hout := outside_profiles μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hf h0 hc hb hg hn
  have hin := inside_endpoints μ W bW hpart S X hX d mX hb haY
  intro c
  apply ThirdsTwinExtraction.endpoint_twin μ (W c) (hW c) (bW c) (sW c) d (ne_of_gt hd) (hr c) X hX mX
  filter_upwards [hout,hin] with u hu hi
  by_cases hus : u∈S
  · exact hi hus c
  · exact endpoint μ (fun x => W c (u,x)) S X hS hX hXS d mX (hu hus c)

lemma three_pairs (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (S X : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (hRG : ∀ᵐ u ∂μ, RowGood μ W u)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h34 : ∀ᵐ u ∂μ, u∈T 3∩T 4 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X)
    (h35 : ∀ᵐ u ∂μ, u∈T 3∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X)
    (h45 : ∀ᵐ u ∂μ, u∈T 4∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 4 (u,x)) X) :
    ∀ᵐ u ∂μ, ∀ i j : Fin 6, 3 ≤ i.val → 3 ≤ j.val → i≠j →
      u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X := by
  filter_upwards [hRG,ae_all_iff.mpr hf,h34,h35,h45] with u hu hfu a34 a35 a45
  have mass (i : Fin 6) (hi : u∈T i) : act μ (W i) (oneSet S) u=d := by
    rw [hfu i]; simp [oneSet,hi]
  intro i j hi hj hij ht
  fin_cases i <;> fin_cases j
  all_goals try (norm_num at hi)
  all_goals try (norm_num at hj)
  all_goals try (norm_num at hij)
  all_goals first
    | exact a34 ht
    | exact a35 ht
    | exact a45 ht
    | exact aligned_complement μ W hW S X hS d hd mS u hu 3 4 (by decide) (mass 3 ht.2) (mass 4 ht.1) (a34 ⟨ht.2,ht.1⟩)
    | exact aligned_complement μ W hW S X hS d hd mS u hu 3 5 (by decide) (mass 3 ht.2) (mass 5 ht.1) (a35 ⟨ht.2,ht.1⟩)
    | exact aligned_complement μ W hW S X hS d hd mS u hu 4 5 (by decide) (mass 4 ht.2) (mass 5 ht.1) (a45 ⟨ht.2,ht.1⟩)
lemma three_nonmixing_twin (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hb : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hg : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (h34 : ∀ᵐ u ∂μ, u∈T 3∩T 4 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X)
    (h35 : ∀ᵐ u ∂μ, u∈T 3∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X)
    (h45 : ∀ᵐ u ∂μ, u∈T 4∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 4 (u,x)) X) :
    ∀ c, ∃ U : Set Ω, MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈X → W c p=oneSet U p.2) := by
  exact no_mixing_twin μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hf h0 hc hb hg haY
    (three_pairs μ W hW S X hS d hd mS T (rowGood_ae μ W bW sW hpart) hf h34 h35 h45)
end ThirdsCaseBNoMixing
end JigBundleModule127

/- Inlined module ThirdsAlignedFamilySplit; original SHA256 94f59c1459955191bc4651cbfad9e7f435d488210e661dc62e134f01ff28b8c9 -/
section JigBundleModule128
open MeasureTheory
namespace ThirdsAlignedFamilySplit
open TwoPairHalfSetOperator ThirdsCaseBNoMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma split_family (F G : Ω×Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (bF : ∀ᵐ p ∂μ.prod μ, 0≤F p ∧ F p≤1) (bG : ∀ᵐ p ∂μ.prod μ, 0≤G p ∧ G p≤1)
    (S X I : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hI : MeasurableSet I) (hXS : X⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d) (mX : μ.real X=d) (mI : μ.real I=d)
    (rF : ∀ᵐ u ∂μ, ∫ x, F (u,x) ∂μ=d) (rG : ∀ᵐ u ∂μ, ∫ x, G (u,x) ∂μ=d)
    (hpart : ∀ᵐ u ∂μ, u∈I → ∀ᵐ x ∂ProbabilityTheory.cond μ S, F (u,x)+G (u,x)=1)
    (halign : ∀ᵐ u ∂μ, u∈I → Aligned (ProbabilityTheory.cond μ S) (fun x => F (u,x)) X) :
    ∃ IX IY : Set Ω, MeasurableSet IX ∧ MeasurableSet IY ∧ IX⊆I ∧ IY⊆I ∧
      Disjoint IX IY ∧ IX∪IY=I ∧ μ.real IX+μ.real IY=d ∧
      (∀ᵐ u ∂μ, u∈IX → ((fun x => F (u,x)) =ᵐ[μ] oneSet X) ∧ ((fun x => G (u,x)) =ᵐ[μ] oneSet (S\X))) ∧
      (∀ᵐ u ∂μ, u∈IY → ((fun x => F (u,x)) =ᵐ[μ] oneSet (S\X)) ∧ ((fun x => G (u,x)) =ᵐ[μ] oneSet X)) := by
  let ν := ProbabilityTheory.cond μ S
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have ey : (fun x => 1-oneSet X x) =ᵐ[ν] oneSet (S\X) := by
    apply ThirdsNormalizedRestriction.conditional_ae μ S hS
    exact Filter.Eventually.of_forall (fun x hx => by by_cases hxx : x∈X <;> simp [oneSet,hx,hxx])
  have hfull : ∀ᵐ u ∂μ, u∈I →
      (((fun x => F (u,x)) =ᵐ[μ] oneSet X) ∧ ((fun x => G (u,x)) =ᵐ[μ] oneSet (S\X))) ∨
      (((fun x => F (u,x)) =ᵐ[μ] oneSet (S\X)) ∧ ((fun x => G (u,x)) =ᵐ[μ] oneSet X)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod bF,Measure.ae_ae_of_ae_prod bG,rF,rG,hpart,halign] with u bu cu ru su pu au
    intro hui
    rcases au hui with ax | ay
    · left
      have gy : (fun x => G (u,x)) =ᵐ[ν] oneSet (S\X) := by
        filter_upwards [pu hui,ax,ey] with x px fx ex
        linarith
      exact ⟨ThirdsFullTargetRow.extend μ (fun x => F (u,x)) (by fun_prop) bu S X hS hX hXS d ru mX ax,
        ThirdsFullTargetRow.extend μ (fun x => G (u,x)) (by fun_prop) cu S (S\X) hS hY Set.sdiff_subset d su mY gy⟩
    · right
      have gx : (fun x => G (u,x)) =ᵐ[ν] oneSet X := by
        filter_upwards [pu hui,ay] with x px fx
        linarith
      exact ⟨ThirdsFullTargetRow.extend μ (fun x => F (u,x)) (by fun_prop) bu S (S\X) hS hY Set.sdiff_subset d ru mY (ay.trans ey),
        ThirdsFullTargetRow.extend μ (fun x => G (u,x)) (by fun_prop) cu S X hS hX hXS d su mX gx⟩
  let t := fun u => ∫ x in X, F (u,x) ∂μ
  have ht : Measurable t := by dsimp [t]; fun_prop
  let IX := I∩{u | t u=d}
  let IY := I\IX
  have hIX : MeasurableSet IX := hI.inter (measurableSet_eq_fun ht measurable_const)
  have hIY : MeasurableSet IY := hI.diff hIX
  have subX : IX⊆I := Set.inter_subset_left
  have subY : IY⊆I := Set.sdiff_subset
  have dis : Disjoint IX IY := Set.disjoint_sdiff_right
  have cover : IX∪IY=I := by
    ext u
    constructor
    · intro hu; rcases hu with hu | hu; exact subX hu; exact subY hu
    · intro hu; by_cases hx : u∈IX; exact Or.inl hx; exact Or.inr ⟨hu,hx⟩
  have mass : μ.real IX+μ.real IY=d := by
    have hh := measureReal_union_add_inter₀ (μ := μ) (s := IX) hIY.nullMeasurableSet
    rw [cover,Set.disjoint_iff_inter_eq_empty.mp dis] at hh
    simpa [mI] using hh.symm
  have tx (u : Ω) (he : (fun x => F (u,x)) =ᵐ[μ] oneSet X) : t u=d := by
    dsimp [t]
    rw [integral_congr_ae (ae_restrict_of_ae he)]
    simp [oneSet,integral_indicator hX,mX]
  have ty (u : Ω) (he : (fun x => F (u,x)) =ᵐ[μ] oneSet (S\X)) : t u=0 := by
    dsimp [t]
    have hz : ∀ᵐ x ∂μ.restrict X, F (u,x)=0 := by
      apply (ae_restrict_iff' hX).mpr
      filter_upwards [he] with x hx
      intro hxx; simpa [oneSet,hxx] using hx
    rw [integral_congr_ae hz]
    simp
  refine ⟨IX,IY,hIX,hIY,subX,subY,dis,cover,mass,?_,?_⟩
  · filter_upwards [hfull] with u hu
    intro hui
    rcases hu hui.1 with hx | hy
    · exact hx
    · have hzero := ty u hy.1
      have heq : t u=d := hui.2
      exfalso; linarith
  · filter_upwards [hfull] with u hu
    intro hui
    rcases hu hui.1 with hx | hy
    · exact (hui.2 ⟨hui.1,tx u hx.1⟩).elim
    · exact hy
end ThirdsAlignedFamilySplit
end JigBundleModule128

/- Inlined module ThirdsMixingRelabel; original SHA256 50ba638e0026f58bd1b499a5b049071b867a9ad94af8e41f952078ff106d9735 -/
section JigBundleModule129
open MeasureTheory
namespace ThirdsMixingRelabel
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter ThirdsCaseBNoMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma alignment_reverse (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (S X : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (hRG : ∀ᵐ u ∂μ, RowGood μ W u)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (i j : Fin 6) (hij : i≠j)
    (ha : ∀ᵐ u ∂μ, u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X) :
    ∀ᵐ u ∂μ, u∈T j∩T i → Aligned (ProbabilityTheory.cond μ S) (fun x => W j (u,x)) X := by
  filter_upwards [hRG,ae_all_iff.mpr hf,ha] with u hu hfu hau
  intro ht
  have mass (c : Fin 6) (hc : u∈T c) : act μ (W c) (oneSet S) u=d := by
    rw [hfu c]; simp [oneSet,hc]
  exact aligned_complement μ W hW S X hS d hd mS u hu i j hij
    (mass i ht.2) (mass j ht.1) (hau ⟨ht.2,ht.1⟩)
lemma mixing_reverse (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (S X : Set Ω) (hS : MeasurableSet S) (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d)
    (T : Fin 6 → Set Ω) (hRG : ∀ᵐ u ∂μ, RowGood μ W u)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (i j : Fin 6) (hij : i≠j)
    (ha : ¬ (∀ᵐ u ∂μ, u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X)) :
    ¬ (∀ᵐ u ∂μ, u∈T j∩T i → Aligned (ProbabilityTheory.cond μ S) (fun x => W j (u,x)) X) := by
  intro hb
  exact ha (alignment_reverse μ W hW S X hS d hd mS T hRG hf j i (Ne.symm hij) hb)
end ThirdsMixingRelabel
end JigBundleModule129

/- Inlined module ThirdsOneMixingLayout; original SHA256 1f36833e3bfb385a971d96ab3c177e07267579e07e00156600001969bf2ab438 -/
section JigBundleModule130
open MeasureTheory
namespace ThirdsOneMixingLayout
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly ThirdsCaseBNoMixing ThirdsSelectedCenter
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma variable_family_split (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (i j : Fin 6) (hij : i≠j) (mI : pairMass μ T S i j=d)
    (ha : ∀ᵐ u ∂μ, u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X) :
    ∃ IX IY : Set Ω, MeasurableSet IX ∧ MeasurableSet IY ∧ IX⊆(T i∩T j)\S ∧ IY⊆(T i∩T j)\S ∧
      Disjoint IX IY ∧ IX∪IY=(T i∩T j)\S ∧ μ.real IX+μ.real IY=d ∧
      (∀ᵐ u ∂μ, u∈IX → ((fun x => W j (u,x)) =ᵐ[μ] oneSet X) ∧ ((fun x => W i (u,x)) =ᵐ[μ] oneSet (S\X))) ∧
      (∀ᵐ u ∂μ, u∈IY → ((fun x => W j (u,x)) =ᵐ[μ] oneSet (S\X)) ∧ ((fun x => W i (u,x)) =ᵐ[μ] oneSet X)) := by
  have hRG := rowGood_ae μ W bW sW hpart
  have haj := ThirdsMixingRelabel.alignment_reverse μ W hW S X hS d hd mS T hRG hf i j hij ha
  have halign : ∀ᵐ u ∂μ, u∈(T i∩T j)\S → Aligned (ProbabilityTheory.cond μ S) (fun x => W j (u,x)) X := by
    filter_upwards [haj] with u hu
    intro ht; exact hu ⟨ht.1.2,ht.1.1⟩
  have sumrows : ∀ᵐ u ∂μ, u∈(T i∩T j)\S → ∀ᵐ x ∂ProbabilityTheory.cond μ S, W j (u,x)+W i (u,x)=1 := by
    filter_upwards [hRG,ae_all_iff.mpr hf] with u hu hfu
    intro ht
    have mass (c : Fin 6) (hc : u∈T c) : act μ (W c) (oneSet S) u=d := by
      rw [hfu c]; simp [oneSet,hc]
    obtain ⟨r,hr,br,mr,ej,ei,hb⟩ := selected_center μ W hW S hS d hd mS u hu j i (Ne.symm hij)
      (mass j ht.1.2) (mass i ht.1.1)
    filter_upwards [ej,ei] with x hj hi
    linarith
  exact ThirdsAlignedFamilySplit.split_family μ (W j) (W i) (hW j) (hW i) (bW j) (bW i)
    S X ((T i∩T j)\S) hS hX (((hT i).inter (hT j)).diff hS) hXS d hd mS mX mI
    (hr j) (hr i) sumrows halign
end ThirdsOneMixingLayout
end JigBundleModule130

/- Inlined module ThirdsOneMixingIndependent; original SHA256 a6a202a776c5488ddb38b222d0ca11131f306ed690d5f0f3680dade05545b9ca -/
section JigBundleModule131
open MeasureTheory
namespace ThirdsOneMixingIndependent
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma split_return (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (Z X Y I₀ I₁ : Set Ω) (pX : μ X≠0) (pY : μ Y≠0)
    (pI : μ I₀≠0 ∨ μ I₁≠0)
    (f4 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈I₀∪I₁ → W 4 p=1)
    (d0 : ∀ᵐ p ∂μ.prod μ, p.1∈I₀ → p.2∈Y → W 3 p=1)
    (d1 : ∀ᵐ p ∂μ.prod μ, p.1∈I₁ → p.2∈X → W 3 p=1)
    (cl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈X → W 1 p=1)
    (cl2 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈Y → W 2 p=1)
    (fb : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈Y → W 1 p=1)
    (fc : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈X → W 2 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0) :
    ∀ᵐ r ∂μ, ∀ᵐ z₀ ∂μ, z₀∈Z → ∀ᵐ z₁ ∂μ, z₁∈Z → W 0 (z₁,r)*W 5 (r,z₀)=0 := by
  have rb : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈Z → W 1 p=1 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae fb,sW 1] with p hf hs
    intro hy hz
    rw [hs]
    exact hf hz hy
  have rc : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Z → W 2 p=1 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae fc,sW 2] with p hf hs
    intro hx hz
    rw [hs]
    exact hf hz hx
  rcases pI with pI | pI
  · let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![4,3,2,1,0,5] (by decide)
    have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
      filter_upwards [hpart] with p hp
      rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
    have f4' : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈I₀ → W 4 p=1 := by
      filter_upwards [f4] with p hf
      exact fun hz hi => hf hz (Or.inl hi)
    exact ThirdsIndependentAnchorColumns.four_full_edges μ (fun c => W (σ c))
      (fun c => hW (σ c)) (fun c => bW (σ c)) (fun c => sW (σ c)) part
      Z I₀ Y Y pI pY pY f4' d0 cl2 rb (hz σ)
  · let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![4,3,1,2,0,5] (by decide)
    have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
      filter_upwards [hpart] with p hp
      rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
    have f4' : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈I₁ → W 4 p=1 := by
      filter_upwards [f4] with p hf
      exact fun hz hi => hf hz (Or.inr hi)
    exact ThirdsIndependentAnchorColumns.four_full_edges μ (fun c => W (σ c))
      (fun c => hW (σ c)) (fun c => bW (σ c)) (fun c => sW (σ c)) part
      Z I₁ X X pI pX pX f4' d1 cl1 rc (hz σ)
end ThirdsOneMixingIndependent
end JigBundleModule131

/- Inlined module ThirdsFourTargetsResidual; original SHA256 609805c6f3d6119e7650526c8302aea7fe2f1be9e99ee5d1f26a9cff07b9c44a -/
section JigBundleModule132
open MeasureTheory
namespace ThirdsFourTargetsResidual
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma residual (W : Fin 6 → Ω×Ω → ℝ)
    (hb : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p)
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X Z I J : Set Ω) (hXS : X⊆S)
    (h1 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → W 1 p=oneSet (S\X) p.2)
    (h2 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → W 2 p=oneSet X p.2)
    (h3 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → W 3 p=oneSet J p.2)
    (h4 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → W 4 p=oneSet I p.2) :
    (∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈Sᶜ\(I∪J) → W 0 p+W 5 p=1) ∧
    (∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∉Sᶜ\(I∪J) → W 0 p=0 ∧ W 5 p=0) := by
  have hi (y : Ω) : oneSet (S\X) y+oneSet X y=oneSet S y := by
    classical
    by_cases hx : y∈X
    · simp [oneSet,hx,hXS hx]
    · by_cases hs : y∈S <;> simp [oneSet,hx,hs]
  have hs : ∀ᵐ p ∂μ.prod μ, p.1∈Z →
      W 0 p+W 5 p=1-oneSet S p.2-oneSet I p.2-oneSet J p.2 := by
    filter_upwards [hpart,h1,h2,h3,h4] with p hp h1 h2 h3 h4
    intro hz
    have h1' := h1 hz
    have h2' := h2 hz
    have h3' := h3 hz
    have h4' := h4 hz
    simp only [Fin.sum_univ_six] at hp
    linarith [hi p.2]
  constructor
  · filter_upwards [hs] with p hp
    intro hz hr
    have hns : p.2∉S := hr.1
    have hni : p.2∉I := fun h => hr.2 (Or.inl h)
    have hnj : p.2∉J := fun h => hr.2 (Or.inr h)
    simpa [oneSet,hns,hni,hnj] using hp hz
  · filter_upwards [hs,hb 0,hb 5] with p hp h0 h5
    intro hz hr
    have he : p.2∈S ∨ p.2∈I ∨ p.2∈J := by
      classical
      simpa only [Set.mem_sdiff,Set.mem_compl_iff,Set.mem_union,not_and_or,not_not] using hr
    have hge : 1≤oneSet S p.2+oneSet I p.2+oneSet J p.2 := by
      rcases he with he|he|he
      · have hh : oneSet S p.2=1 := by simp [oneSet,he]
        linarith [(oneSet_bounds I p.2).1,(oneSet_bounds J p.2).1]
      · have hh : oneSet I p.2=1 := by simp [oneSet,he]
        linarith [(oneSet_bounds S p.2).1,(oneSet_bounds J p.2).1]
      · have hh : oneSet J p.2=1 := by simp [oneSet,he]
        linarith [(oneSet_bounds S p.2).1,(oneSet_bounds I p.2).1]
    have hh := hp hz
    constructor <;> linarith
end ThirdsFourTargetsResidual
end JigBundleModule132

/- Inlined module ThirdsBinaryColumnTarget; original SHA256 268fc1f97e24b20c64f1236caca359f1937d8919d1f42c81fcd752916a0a9cb5 -/
section JigBundleModule133
open MeasureTheory
namespace ThirdsBinaryColumnTarget
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma target (A : Ω × Ω → ℝ) (hA : Measurable A)
    (Z R : Set Ω) (hZ : MeasurableSet Z) (hR : MeasurableSet R) (pZ : μ Z ≠ 0)
    (d : ℝ) (hr : ∀ᵐ z ∂μ.restrict Z, (∫ r, A (z,r) ∂μ) = d)
    (hb : ∀ᵐ r ∂μ, r ∈ R →
      ((fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 0) ∨
      ((fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 1))
    (ho : ∀ᵐ r ∂μ, r ∉ R → (fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 0) :
    ∃ S : Set Ω, MeasurableSet S ∧ S ⊆ R ∧ μ.real S = d ∧
      ∀ᵐ z ∂μ.restrict Z, (fun r => A (z,r)) =ᵐ[μ] oneSet S := by
  classical
  let a : Ω → ℝ := fun r => ∫ z in Z, A (z,r) ∂μ
  have ha : Measurable a := hA.stronglyMeasurable.integral_prod_left'.measurable
  let S : Set Ω := R ∩ {r | 0 < a r}
  have hS : MeasurableSet S := hR.inter (measurableSet_lt measurable_const ha)
  have mZ : 0 < μ.real Z := by
    exact ENNReal.toReal_pos pZ (measure_ne_top μ Z)
  have hc : ∀ᵐ r ∂μ, ∀ᵐ z ∂μ.restrict Z, A (z,r) = oneSet S r := by
    filter_upwards [hb,ho] with r hb ho
    by_cases hrR : r ∈ R
    · rcases hb hrR with hh | hh
      · have hz : a r = 0 := by
          dsimp [a]
          rw [integral_congr_ae hh, integral_zero]
        filter_upwards [hh] with z hz'
        simp [oneSet,S,hrR,hz,hz']
      · have hz : a r = μ.real Z := by
          dsimp [a]
          rw [integral_congr_ae hh]
          simp
        filter_upwards [hh] with z hz'
        simp [oneSet,S,hrR,hz,mZ,hz']
    · filter_upwards [ho hrR] with z hz'
      simp [oneSet,S,hrR,hz']
  have hprod : ∀ᵐ p ∂μ.prod (μ.restrict Z), A (p.2,p.1) = oneSet S p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (by fun_prop) ((oneSet_measurable S hS).comp measurable_fst))).mpr
    exact hc
  have hrows : ∀ᵐ z ∂μ.restrict Z, (fun r => A (z,r)) =ᵐ[μ] oneSet S :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod)
  have hchoose : ∀ᵐ z ∂μ.restrict Z,
      (∫ r, A (z,r) ∂μ) = d ∧ (fun r => A (z,r)) =ᵐ[μ] oneSet S := hr.and hrows
  obtain ⟨z,hzZ,hzr,hze⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pZ hchoose
  have hm : μ.real S = d := by
    rw [integral_congr_ae hze] at hzr
    simpa [oneSet,integral_indicator hS] using hzr
  exact ⟨S,hS,Set.inter_subset_left,hm,hrows⟩

end ThirdsBinaryColumnTarget
end JigBundleModule133

/- Inlined module ThirdsOneMixingTarget; original SHA256 586457f806ef033891660faaa5393e3eb76d9d3c0d82ebb1627da6b2de054401 -/
section JigBundleModule134
open MeasureTheory
namespace ThirdsOneMixingTarget
open TwoPairHalfSetOperator ThirdsIndependentAnchorColumns
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma from_independent_zero (A F : Ω × Ω → ℝ) (hA : Measurable A)
    (sF : ∀ᵐ p ∂μ.prod μ, F p=F (p.2,p.1))
    (Z R : Set Ω) (hZ : MeasurableSet Z) (hR : MeasurableSet R) (pZ : μ Z≠0)
    (d : ℝ) (hr : ∀ᵐ z ∂μ, ∫ r, A (z,r) ∂μ=d)
    (hc : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈R → A p+F p=1)
    (ho : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∉R → A p=0)
    (hz : ∀ᵐ r ∂μ, ∀ᵐ z₀ ∂μ, z₀∈Z → ∀ᵐ z₁ ∂μ, z₁∈Z → A (z₁,r)*F (r,z₀)=0) :
    ∃ Q : Set Ω, MeasurableSet Q ∧ Q⊆R ∧ μ.real Q=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈Z → A p=oneSet Q p.2) := by
  have hcs := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (hc.and sF))
  have hos := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae ho)
  have hb : ∀ᵐ r ∂μ, r∈R → ((fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 0) ∨
      ((fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 1) := by
    filter_upwards [hcs,hz] with r hcr hzr
    intro hrr
    apply independent_binary (μ.restrict Z) (fun z => A (z,r)) (fun z => F (r,z))
    · apply (ae_restrict_iff' hZ).mpr
      filter_upwards [hcr] with z hcz
      intro hzz
      have hs : F (z,r)=F (r,z) := hcz.2
      rw [← hs]
      exact hcz.1 hzz hrr
    · apply (ae_restrict_iff' hZ).mpr
      filter_upwards [hzr] with z hz
      intro hzz
      exact (ae_restrict_iff' hZ).mpr (hz hzz)
  have houtside : ∀ᵐ r ∂μ, r∉R → (fun z => A (z,r)) =ᵐ[μ.restrict Z] fun _ => 0 := by
    filter_upwards [hos] with r hor
    intro hrr
    apply (ae_restrict_iff' hZ).mpr
    filter_upwards [hor] with z hz
    intro hzz
    exact hz hzz hrr
  obtain ⟨Q,hQ,hQR,mQ,hfull⟩ := ThirdsBinaryColumnTarget.target μ A hA Z R hZ hR pZ d
    (ae_restrict_of_ae hr) hb houtside
  refine ⟨Q,hQ,hQR,mQ,?_⟩
  apply (Measure.ae_prod_iff_ae_ae ((hZ.preimage measurable_fst).imp
    (measurableSet_eq_fun hA ((oneSet_measurable Q hQ).comp measurable_snd)))).mpr
  have hf := (ae_restrict_iff' hZ).mp hfull
  filter_upwards [hf] with z hz
  by_cases hzz : z∈Z
  · filter_upwards [hz hzz] with r hr
    exact fun _ => hr
  · exact Filter.Eventually.of_forall (fun _ hh => False.elim (hzz hh))
end ThirdsOneMixingTarget
end JigBundleModule134

/- Inlined module ThirdsOneMixingATarget; original SHA256 2661cf2018cf9b658022e1e721b6e43f82eeaaf32be363ffde7cf80615adef72 -/
section JigBundleModule135
open MeasureTheory
namespace ThirdsOneMixingATarget
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly ThirdsCaseBNoMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma rectangle_of_rows (A : Ω×Ω → ℝ) (hA : Measurable A)
    (Z U : Set Ω) (hZ : MeasurableSet Z) (hU : MeasurableSet U)
    (hf : ∀ᵐ z ∂μ, z∈Z → (fun x => A (z,x)) =ᵐ[μ] oneSet U) :
    ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈U → A p=1 := by
  apply (Measure.ae_prod_iff_ae_ae ((hZ.preimage measurable_fst).imp
    ((hU.preimage measurable_snd).imp (measurableSet_eq_fun hA measurable_const)))).mpr
  filter_upwards [hf] with z hf
  by_cases hz : z∈Z
  · filter_upwards [hf hz] with x hx
    intro _ hu
    simpa [oneSet,hu] using hx
  · exact Filter.Eventually.of_forall (fun x hh => (hz hh).elim)
lemma a_target (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0)
    (ha35 : ∀ᵐ u ∂μ, u∈T 3∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X) :
    ∃ Q : Set Ω, MeasurableSet Q ∧ Q⊆Sᶜ\(((T 3∩T 5)\S)∪((T 4∩T 5)\S)) ∧ μ.real Q=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 0 p=oneSet Q p.2) := by
  obtain ⟨pZ,mH,mI,mJ,f1,f2,f3,f4⟩ := ThirdsOneMixingFourTargets.four_targets
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  obtain ⟨I₀,I₁,hI₀,hI₁,sub₀,sub₁,dis,cover,msplit,rows₀,rows₁⟩ :=
    ThirdsOneMixingLayout.variable_family_split μ W hW bW sW hpart S X hS hX hXS
      d hd mS mX hr T hT hf 3 5 (by decide) mI ha35
  have hZ : MeasurableSet ((T 1∩T 2)\S) := ((hT 1).inter (hT 2)).diff hS
  have hI : MeasurableSet ((T 3∩T 5)\S) := ((hT 3).inter (hT 5)).diff hS
  have hJ : MeasurableSet ((T 4∩T 5)\S) := ((hT 4).inter (hT 5)).diff hS
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have pX : μ X≠0 := by intro he; simp [measureReal_def,he] at mX; linarith
  have pY : μ (S\X)≠0 := by intro he; simp [measureReal_def,he] at mY; linarith
  have pZ' : μ ((T 1∩T 2)\S)≠0 := by
    intro he
    change 0<μ.real ((T 1∩T 2)\S) at pZ
    simp [measureReal_def,he] at pZ
  have rd₀ := rectangle_of_rows μ (W 3) (hW 3) I₀ (S\X) hI₀ hY
    (rows₀.mono (fun _ h hz => (h hz).2))
  have rd₁ := rectangle_of_rows μ (W 3) (hW 3) I₁ X hI₁ hX
    (rows₁.mono (fun _ h hz => (h hz).2))
  have ff4 : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈I₀∪I₁ → W 4 p=1 := by
    filter_upwards [f4] with p hp
    intro hz hi
    have hh : p.2∈(T 3∩T 5)\S := by rw [← cover]; exact hi
    simpa [oneSet,hh] using hp hz
  have cl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈X → W 1 p=1 := by
    filter_upwards [hcl1] with p hp
    intro hx hy; simpa [oneSet,hy] using hp hx
  have cl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → p.2∈S\X → W 2 p=1 := by
    filter_upwards [hcl2] with p hp
    intro hx hy; simpa [oneSet,hy] using hp hx
  have fb : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈S\X → W 1 p=1 := by
    filter_upwards [f1] with p hp
    intro hx hy; simpa [oneSet,hy] using hp hx
  have fc : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈X → W 2 p=1 := by
    filter_upwards [f2] with p hp
    intro hx hy; simpa [oneSet,hy] using hp hx
  have hzind := ThirdsOneMixingIndependent.split_return μ W hW bW sW hpart
    ((T 1∩T 2)\S) X (S\X) I₀ I₁ pX pY
    (ThirdsOneMixingHZero.positive_split μ I₀ I₁ d hd msplit) ff4 rd₀ rd₁ cl1 cl2 fb fc hz
  obtain ⟨res,out⟩ := ThirdsFourTargetsResidual.residual μ W (fun c => (bW c).mono fun _ h => h.1)
    hpart S X ((T 1∩T 2)\S) ((T 3∩T 5)\S) ((T 4∩T 5)\S) hXS f1 f2 f3 f4
  exact ThirdsOneMixingTarget.from_independent_zero μ (W 0) (W 5) (hW 0) (sW 5)
    ((T 1∩T 2)\S) (Sᶜ\(((T 3∩T 5)\S)∪((T 4∩T 5)\S))) hZ (hS.compl.diff (hI.union hJ))
    pZ' d (hr 0) res (out.mono (fun _ h hz hr => (h hz hr).1)) hzind
end ThirdsOneMixingATarget
end JigBundleModule135

/- Inlined module ThirdsOneMixingTwin; original SHA256 4690223d18284b40ce4498551927e4e83963d4d2d9d1a6222ee74e825d20b890 -/
section JigBundleModule136
open MeasureTheory
namespace ThirdsOneMixingTwin
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly ThirdsCaseBNoMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma twin_of_mass (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0)
    (ha35 : ∀ᵐ u ∂μ, u∈T 3∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X)
    (mZ : pairMass μ T S 1 2=d) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
  classical
  obtain ⟨pZ,mH,mI,mJ,f1,f2,f3,f4⟩ := ThirdsOneMixingFourTargets.four_targets
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  obtain ⟨Q,hQ,subQ,mQ,fQ⟩ := ThirdsOneMixingATarget.a_target
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF ha35
  have hY : MeasurableSet (S\X) := hS.diff hX
  have hI : MeasurableSet ((T 3∩T 5)\S) := ((hT 3).inter (hT 5)).diff hS
  have hJ : MeasurableSet ((T 4∩T 5)\S) := ((hT 4).inter (hT 5)).diff hS
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have htargets : ∀ c : Fin 6, c≠5 → ∃ U : Set Ω, MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
    intro c hn5
    fin_cases c
    · exact ⟨Q,hQ,mQ,fQ⟩
    · exact ⟨S\X,hY,mY,f1⟩
    · exact ⟨X,hX,mX,f2⟩
    · exact ⟨(T 4∩T 5)\S,hJ,mJ,f3⟩
    · exact ⟨(T 3∩T 5)\S,hI,mI,f4⟩
    · exact (hn5 rfl).elim
  have hne (i : Fin 5) : i.castSucc≠(5:Fin 6) := by fin_cases i <;> decide
  choose G hG mG fG using (fun i : Fin 5 => htargets i.castSucc (hne i))
  obtain ⟨R,hR,mR,fR⟩ := ThirdsSixthTarget.sixth_target μ W
    ((bW 5).mono fun _ h => h.1) hpart d (hr 5) ((T 1∩T 2)\S) pZ G hG fG
  refine ⟨mZ,?_⟩
  intro c
  by_cases hc5 : c=5
  · subst c; exact ⟨R,hR,mR,fR⟩
  · exact htargets c hc5
end ThirdsOneMixingTwin
end JigBundleModule136

/- Inlined module ThirdsOneMixingSplitExclusion; original SHA256 b2fb6186839a6f63ac257336040db19fae9c07eacc6d1907cbe9419f33447338 -/
section JigBundleModule137
open MeasureTheory
namespace ThirdsOneMixingSplitExclusion
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma split_exclusion (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (Z X Y I₀ I₁ : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hI₀ : MeasurableSet I₀) (hI₁ : MeasurableSet I₁)
    (pY : μ Y≠0) (pI : μ I₀≠0 ∨ μ I₁≠0)
    (rows₀ : ∀ᵐ u ∂μ, u∈I₀ → ((fun x => W 5 (u,x)) =ᵐ[μ] oneSet X) ∧
      ((fun x => W 3 (u,x)) =ᵐ[μ] oneSet Y))
    (rows₁ : ∀ᵐ u ∂μ, u∈I₁ → ((fun x => W 5 (u,x)) =ᵐ[μ] oneSet Y) ∧
      ((fun x => W 3 (u,x)) =ᵐ[μ] oneSet X))
    (fb : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈Y → W 1 p=1)
    (cl2 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈Y → W 2 p=1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0) :
    ∀ᵐ h ∂μ, ∀ᵐ z ∂μ, z∈Z → W 0 (h,z)*(∫ x in X, W 4 (h,x) ∂μ)=0 := by
  have d0 := ThirdsOneMixingATarget.rectangle_of_rows μ (W 3) (hW 3) I₀ Y hI₀ hY
    (rows₀.mono (fun _ h hz => (h hz).2))
  have f0 := ThirdsOneMixingATarget.rectangle_of_rows μ (W 5) (hW 5) I₀ X hI₀ hX
    (rows₀.mono (fun _ h hz => (h hz).1))
  have d1 := ThirdsOneMixingATarget.rectangle_of_rows μ (W 3) (hW 3) I₁ X hI₁ hX
    (rows₁.mono (fun _ h hz => (h hz).2))
  have f1 := ThirdsOneMixingATarget.rectangle_of_rows μ (W 5) (hW 5) I₁ Y hI₁ hY
    (rows₁.mono (fun _ h hz => (h hz).1))
  have rd0 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈I₀ → W 3 p=1 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae d0,sW 3] with p hf hs
    intro hy hi; rw [hs]; exact hf hi hy
  have rf1 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈I₁ → W 5 p=1 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae f1,sW 5] with p hf hs
    intro hy hi; rw [hs]; exact hf hi hy
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![1,2,3,5,4,0] (by decide)
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have hs : LowSupportCycle.cycleNested (μ := μ)
      (fun i => W (σ ((Equiv.swap (2:Fin 6) 3) i)))=0 := hz ((Equiv.swap 2 3).trans σ)
  exact ThirdsOneMixingHZero.two_split μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) part Z Y I₀ I₁ X hX pY pI
    fb cl2 rd0 f0 rf1 d1 (hz σ) hs
end ThirdsOneMixingSplitExclusion
end JigBundleModule137

/- Inlined module ThirdsOneMixingPairIntegral; original SHA256 49f3c842c2e15e70dabc6d811dbb588b69ea505da1b6f0d6ef7b4dac6ce168a3 -/
section JigBundleModule138
open MeasureTheory
namespace ThirdsOneMixingPairIntegral
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma pair_integral (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (i j : Fin 6) (hij : i≠j) :
    ∀ᵐ u ∂μ, u∈T i∩T j → (∫ x in X, W i (u,x) ∂μ)+(∫ x in X, W j (u,x) ∂μ)=d := by
  have hRG := rowGood_ae μ W bW sW hpart
  filter_upwards [hRG,ae_all_iff.mpr hf] with u hu hfu
  intro ht
  have mass (c : Fin 6) (hc : u∈T c) : act μ (W c) (oneSet S) u=d := by
    rw [hfu c]; simp [oneSet,hc]
  obtain ⟨r,hr,br,mr,ei,ej,hb⟩ := selected_center μ W hW S hS d hd mS u hu i j hij
    (mass i ht.1) (mass j ht.2)
  have hsum : ∀ᵐ x ∂ProbabilityTheory.cond μ S, W i (u,x)+W j (u,x)=1 := by
    filter_upwards [ei,ej] with x hi hj
    linarith
  have hs : ∀ᵐ x ∂μ.restrict S, W i (u,x)+W j (u,x)=1 :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top μ S))).mp hsum
  have hx : ∀ᵐ x ∂μ.restrict X, W i (u,x)+W j (u,x)=1 := by
    apply (ae_restrict_iff' hX).mpr
    filter_upwards [(ae_restrict_iff' hS).mp hs] with x hx
    exact fun hh => hx (hXS hh)
  have ii := LowSupportAnalysis.unit_integrable_ae (μ := μ) (f := fun x => W i (u,x))
    (by fun_prop) ((hu.1 i).mono fun _ h => ⟨h.1,h.2.1⟩)
  have ij := LowSupportAnalysis.unit_integrable_ae (μ := μ) (f := fun x => W j (u,x))
    (by fun_prop) ((hu.1 j).mono fun _ h => ⟨h.1,h.2.1⟩)
  rw [← integral_add (ii.restrict (s := X)) (ij.restrict (s := X)),integral_congr_ae hx]
  simpa using mX
end ThirdsOneMixingPairIntegral
end JigBundleModule138

/- Inlined module ThirdsOneMixingActualHZero; original SHA256 cf144693f808df884c22249ff691da78a825a9312be235eb8d404011eb9c177a -/
section JigBundleModule139
open MeasureTheory
namespace ThirdsOneMixingActualHZero
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly ThirdsCaseBNoMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma h_zero (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0)
    (ha35 : ∀ᵐ u ∂μ, u∈T 3∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X)
    (ha45 : ∀ᵐ u ∂μ, u∈T 4∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 4 (u,x)) X) :
    ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 4)\S → W 0 p=0 := by
  obtain ⟨pZ,mH,mI,mJ,f1,f2,f3,f4⟩ := ThirdsOneMixingFourTargets.four_targets
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  obtain ⟨I₀,I₁,hI₀,hI₁,subI₀,subI₁,disI,coverI,mIsplit,rowsI₀,rowsI₁⟩ :=
    ThirdsOneMixingLayout.variable_family_split μ W hW bW sW hpart S X hS hX hXS
      d hd mS mX hr T hT hf 3 5 (by decide) mI ha35
  obtain ⟨J₀,J₁,hJ₀,hJ₁,subJ₀,subJ₁,disJ,coverJ,mJsplit,rowsJ₀,rowsJ₁⟩ :=
    ThirdsOneMixingLayout.variable_family_split μ W hW bW sW hpart S X hS hX hXS
      d hd mS mX hr T hT hf 4 5 (by decide) mJ ha45
  have hZ : MeasurableSet ((T 1∩T 2)\S) := ((hT 1).inter (hT 2)).diff hS
  have hH : MeasurableSet ((T 3∩T 4)\S) := ((hT 3).inter (hT 4)).diff hS
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have pY : μ (S\X)≠0 := by intro he; simp [measureReal_def,he] at mY; linarith
  have fb : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈S\X → W 1 p=1 := by
    filter_upwards [f1] with p hp
    intro hx hy; simpa [oneSet,hy] using hp hx
  have cl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → p.2∈S\X → W 2 p=1 := by
    filter_upwards [hcl2] with p hp
    intro hx hy; simpa [oneSet,hy] using hp hx
  have he := ThirdsOneMixingSplitExclusion.split_exclusion μ W hW bW sW hpart
    ((T 1∩T 2)\S) X (S\X) I₀ I₁ hX hY hI₀ hI₁ pY
    (ThirdsOneMixingHZero.positive_split μ I₀ I₁ d hd mIsplit) rowsI₀ rowsI₁ fb cl2 hz
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,1,2,4,3,5] (by decide)
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have cycles : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ (τ c)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have hd' := ThirdsOneMixingSplitExclusion.split_exclusion μ (fun c => W (σ c))
    (fun c => hW (σ c)) (fun c => bW (σ c)) (fun c => sW (σ c)) part
    ((T 1∩T 2)\S) X (S\X) J₀ J₁ hX hY hJ₀ hJ₁ pY
    (ThirdsOneMixingHZero.positive_split μ J₀ J₁ d hd mJsplit) rowsJ₀ rowsJ₁ fb cl2 cycles
  have pair := ThirdsOneMixingPairIntegral.pair_integral μ W hW bW sW hpart S X hS hX hXS
    d hd mS mX T hf 3 4 (by decide)
  exact ThirdsOneMixingHZero.combine_on_rectangle μ (W 0) (W 3) (W 4) (hW 0) (sW 0)
    ((T 1∩T 2)\S) ((T 3∩T 4)\S) X hZ hH d (ne_of_gt hd) he hd'
    (pair.mono (fun _ h hh => h hh.1))
end ThirdsOneMixingActualHZero
end JigBundleModule139

/- Inlined module ThirdsOneMixingFullF; original SHA256 e39f98edf97d040fe8232a47c343fd4dd078cf132ba989ad3801d88d75906c86 -/
section JigBundleModule140
open MeasureTheory
namespace ThirdsOneMixingFullF
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma full_f_on_h (W : Fin 6 → Ω×Ω → ℝ) (T : Fin 6 → Set Ω)
    (hT : ∀ c, MeasurableSet (T c)) (S : Set Ω)
    (hc : ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=2)
    (res : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S →
      p.2∈Sᶜ\(((T 3∩T 5)\S)∪((T 4∩T 5)\S)) → W 0 p+W 5 p=1)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 4)\S → W 0 p=0) :
    ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 4)\S → W 5 p=1 := by
  have hm (c : Fin 6) : Measurable (oneSet (T c) : Ω → ℝ) := oneSet_measurable (T c) (hT c)
  have hp : ∀ᵐ p ∂μ.prod μ, ∑ c, oneSet (T c) p.2=2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun _ => hc)
  filter_upwards [hp,res,hzero] with p hp hr hz
  intro hZ hH
  have n5 : p.2∉T 5 := by
    intro ht
    have h3 : oneSet (T 3) p.2=1 := by simp [oneSet,hH.1.1]
    have h4 : oneSet (T 4) p.2=1 := by simp [oneSet,hH.1.2]
    have h5 : oneSet (T 5) p.2=1 := by simp [oneSet,ht]
    simp only [Fin.sum_univ_six,h3,h4,h5] at hp
    linarith [(oneSet_bounds (T 0) p.2).1,(oneSet_bounds (T 1) p.2).1,(oneSet_bounds (T 2) p.2).1]
  have hR : p.2∈Sᶜ\(((T 3∩T 5)\S)∪((T 4∩T 5)\S)) := by
    refine ⟨hH.2,?_⟩
    rintro (hi|hj)
    · exact n5 hi.1.2
    · exact n5 hj.1.2
  have hh := hr hZ hR
  rw [hz hZ hH,zero_add] at hh
  exact hh
end ThirdsOneMixingFullF
end JigBundleModule140

/- Inlined module ThirdsOneMixingPositiveMass; original SHA256 605b678b0e3ab2dfc1b3ec2a2a2f2d9f2a438ef75e4d44755a30339abb0fe3cc -/
section JigBundleModule141
open MeasureTheory
namespace ThirdsOneMixingPositiveMass
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma positive_double (A : Ω×Ω → ℝ) (hA : Measurable A)
    (bA : ∀ᵐ p ∂μ.prod μ, 0≤A p ∧ A p≤1)
    (H U M : Set Ω) (hH : MeasurableSet H) (pM : μ M≠0) (subM : M⊆H)
    (pos : ∀ᵐ v ∂μ, v∈M → 0<∫ x in U, A (v,x) ∂μ) :
    0<∫ v in H, ∫ x in U, A (v,x) ∂μ ∂μ := by
  have hinner : Measurable (fun v => ∫ x in U, A (v,x) ∂μ) :=
    hA.stronglyMeasurable.integral_prod_right'.measurable
  have bound : ∀ᵐ v ∂μ, 0≤(∫ x in U, A (v,x) ∂μ) ∧ (∫ x in U, A (v,x) ∂μ)≤μ.real U := by
    filter_upwards [Measure.ae_ae_of_ae_prod bA] with v hv
    have ri := LowSupportAnalysis.unit_integrable_ae (μ := μ) (f := fun x => A (v,x)) (by fun_prop) hv
    constructor
    · exact integral_nonneg_of_ae (ae_restrict_of_ae (hv.mono fun _ h => h.1))
    · have hi := integral_mono_ae (ri.restrict (s := U)) (integrable_const (1:ℝ))
        (ae_restrict_of_ae (hv.mono fun _ h => h.2))
      simpa using hi
  have ii : Integrable (fun v => ∫ x in U, A (v,x) ∂μ) μ := by
    apply Integrable.of_bound hinner.aestronglyMeasurable (μ.real U)
    filter_upwards [bound] with v hv
    simpa [Real.norm_eq_abs,abs_of_nonneg hv.1] using hv.2
  have nn : 0≤∫ v in H, ∫ x in U, A (v,x) ∂μ ∂μ :=
    integral_nonneg_of_ae (ae_restrict_of_ae (bound.mono fun _ h => h.1))
  by_contra hn
  have hz : (∫ v in H, ∫ x in U, A (v,x) ∂μ ∂μ)=0 := le_antisymm (le_of_not_gt hn) nn
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (ae_restrict_of_ae (bound.mono fun _ h => h.1)) (ii.restrict (s := H))).mp hz
  have good := pos.and ((ae_restrict_iff' hH).mp hzero)
  obtain ⟨v,hvM,hp,hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pM (ae_restrict_of_ae good)
  have hp' := hp hvM
  have hvz : (∫ x in U, A (v,x) ∂μ)=0 := hz (subM hvM)
  linarith
end ThirdsOneMixingPositiveMass
end JigBundleModule141

/- Inlined module ThirdsOneMixingActualPositive; original SHA256 3add3cc55e9ba6cab5bd52eae94fd233eb0330decbb53017adbb123974d9b69e -/
section JigBundleModule142
open MeasureTheory
namespace ThirdsOneMixingActualPositive
open FourColorKernels TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma four_positive (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (mD : μ.real (S∩T 3)=0) :
    (0<∫ h in (T 3∩T 4)\S, ∫ x in X, W 3 (h,x) ∂μ ∂μ) ∧
    (0<∫ h in (T 3∩T 4)\S, ∫ x in X, W 4 (h,x) ∂μ ∂μ) ∧
    (0<∫ h in (T 3∩T 4)\S, ∫ x in S\X, W 3 (h,x) ∂μ ∂μ) ∧
    (0<∫ h in (T 3∩T 4)\S, ∫ x in S\X, W 4 (h,x) ∂μ ∂μ) := by
  obtain ⟨M,hM,pM,subM,posM⟩ := ThirdsActualMixingSet.mixing_set μ W hW bW sW hpart
    S X hS hX hXS d hd mS mX T hT hf hn
  have pm : 0<μ.real M := ENNReal.toReal_pos pM (measure_ne_top μ M)
  have pn := ThirdsPositiveClass.outside_positive μ M S (T 3) hS pm (fun _ hx => (subM hx).1) mD
  have pN : μ (M\S)≠0 := by intro hn; simp [measureReal_def,hn] at pn
  have subN : M\S⊆(T 3∩T 4)\S := fun _ h => ⟨subM h.1,h.2⟩
  have posN : ∀ᵐ h ∂μ, h∈M\S →
      (0<∫ x in X, W 3 (h,x) ∂μ) ∧ (0<∫ x in X, W 4 (h,x) ∂μ) ∧
      (0<∫ x in S\X, W 3 (h,x) ∂μ) ∧ (0<∫ x in S\X, W 4 (h,x) ∂μ) := by
    filter_upwards [posM,Measure.ae_ae_of_ae_prod (sW 3)] with h hp hs
    intro hh
    have pp := hp hh.1
    have ex : (∫ x in X, W 3 (h,x) ∂μ)=(∫ x in X, W 3 (x,h) ∂μ) :=
      integral_congr_ae (ae_restrict_of_ae hs)
    have ey : (∫ x in S\X, W 3 (h,x) ∂μ)=(∫ x in S\X, W 3 (x,h) ∂μ) :=
      integral_congr_ae (ae_restrict_of_ae hs)
    exact ⟨ex.symm ▸ pp.1,pp.2.1,ey.symm ▸ pp.2.2.1,pp.2.2.2⟩
  have hH : MeasurableSet ((T 3∩T 4)\S) := ((hT 3).inter (hT 4)).diff hS
  exact ⟨ThirdsOneMixingPositiveMass.positive_double μ (W 3) (hW 3) (bW 3)
      ((T 3∩T 4)\S) X (M\S) hH pN subN (posN.mono (fun _ h hx => (h hx).1)),
    ThirdsOneMixingPositiveMass.positive_double μ (W 4) (hW 4) (bW 4)
      ((T 3∩T 4)\S) X (M\S) hH pN subN (posN.mono (fun _ h hx => (h hx).2.1)),
    ThirdsOneMixingPositiveMass.positive_double μ (W 3) (hW 3) (bW 3)
      ((T 3∩T 4)\S) (S\X) (M\S) hH pN subN (posN.mono (fun _ h hx => (h hx).2.2.1)),
    ThirdsOneMixingPositiveMass.positive_double μ (W 4) (hW 4) (bW 4)
      ((T 3∩T 4)\S) (S\X) (M\S) hH pN subN (posN.mono (fun _ h hx => (h hx).2.2.2))⟩
end ThirdsOneMixingActualPositive
end JigBundleModule142

/- Inlined module RootedBowtie; original SHA256 fc628167f283f99648ef67dc1f11e4db5bedbf8811bf1d900329e268be7cebfc -/
section JigBundleModule143
open MeasureTheory
noncomputable section
namespace RootedBowtie
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
abbrev Outer (Ω : Type*) := (Ω × Ω) × (Ω × Ω)
abbrev outerMeasure : Measure (Outer Ω) := (μ.prod μ).prod (μ.prod μ)
def leftSpokes (W : Fin 6 → Ω × Ω → ℝ) (p : Ω × Outer Ω) : ℝ :=
  W 0 (p.1,p.2.1.1) * W 5 (p.2.2.2,p.1)
def rightSpokes (W : Fin 6 → Ω × Ω → ℝ) (p : Ω × Outer Ω) : ℝ :=
  W 2 (p.2.1.2,p.1) * W 3 (p.1,p.2.2.1)
def outerEdges (W : Fin 6 → Ω × Ω → ℝ) (p : Outer Ω) : ℝ :=
  W 1 p.1 * W 4 p.2
def bowtie (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ p, outerEdges W p * (∫ r, leftSpokes W (r,p) * rightSpokes W (r,p) ∂μ)
    ∂outerMeasure μ
def cycle (W : Fin 6 → Ω × Ω → ℝ) : ℝ :=
  ∫ p, ∫ rs, outerEdges W p *
    (leftSpokes W (rs.1,p) * rightSpokes W (rs.2,p)) ∂μ.prod μ ∂outerMeasure μ

/-- The six independent vertices occur cyclically as r,a,b,s,c,d. -/
lemma cycle_expanded (W : Fin 6 → Ω × Ω → ℝ) :
    cycle μ W = ∫ p, ∫ rs,
      W 0 (rs.1,p.1.1) * W 1 p.1 * W 2 (p.1.2,rs.2) *
      W 3 (rs.2,p.2.1) * W 4 p.2 * W 5 (p.2.2,rs.1)
      ∂μ.prod μ ∂outerMeasure μ := by
  unfold cycle
  apply integral_congr_ae
  filter_upwards [] with p
  apply integral_congr_ae
  filter_upwards [] with rs
  unfold outerEdges leftSpokes rightSpokes
  ring

lemma bowtie_sq_le_cycle (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    (bowtie μ W)^2 ≤ cycle μ W := by
  have hF : Measurable (leftSpokes W) := by unfold leftSpokes; fun_prop
  have hG : Measurable (rightSpokes W) := by unfold rightSpokes; fun_prop
  have hH : Measurable (outerEdges W) := by unfold outerEdges; fun_prop
  have bF : ∀ p, 0 ≤ leftSpokes W p ∧ leftSpokes W p ≤ 1 := by
    intro p; exact LowSupportAnalysis.mul_unit (bW 0 _) (bW 5 _)
  have bG : ∀ p, 0 ≤ rightSpokes W p ∧ rightSpokes W p ≤ 1 := by
    intro p; exact LowSupportAnalysis.mul_unit (bW 2 _) (bW 3 _)
  have bH : ∀ p, 0 ≤ outerEdges W p ∧ outerEdges W p ≤ 1 := by
    intro p; exact LowSupportAnalysis.mul_unit (bW 1 _) (bW 4 _)
  have hs := LowSupportAnalysis.vertex_split_square (μ := μ) (ν := outerMeasure μ)
    (leftSpokes W) (rightSpokes W) (outerEdges W) hF hG hH bF bG bH
  change (bowtie μ W)^2 ≤ _ at hs
  convert hs using 1
  unfold cycle
  apply integral_congr_ae
  filter_upwards [] with p
  rw [integral_const_mul]
  congr 1
  exact integral_prod_mul (fun r => leftSpokes W (r,p)) (fun s => rightSpokes W (s,p))

lemma cycle_pos_of_bowtie_pos (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hb : 0 < bowtie μ W) : 0 < cycle μ W := by
  have hs := bowtie_sq_le_cycle μ W hW bW
  nlinarith [sq_pos_of_pos hb]

lemma bowtie_zero_of_cycle_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hc : cycle μ W = 0) : bowtie μ W = 0 := by
  have hs := bowtie_sq_le_cycle μ W hW bW
  rw [hc] at hs
  nlinarith [sq_nonneg (bowtie μ W)]
end RootedBowtie
end

end JigBundleModule143

/- Inlined module RootedBowtieBridge; original SHA256 6832a1a50225735de589043ca69f32e95fbb2234e7119f59af685b832ba33e5b -/
section JigBundleModule144
open MeasureTheory
namespace RootedBowtie
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma cycle_eq_nested (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hb : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1) :
    cycle μ W = LowSupportCycle.cycleNested (μ := μ) W := by
  rw [cycle_expanded]
  rw [integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))]
  rw [integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))]
  simp only
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext b
    rw [integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))]
    arg 2
    ext c
    arg 2
    ext d
    rw [integral_prod _ (LowSupportAnalysis.unit_integrable (by fun_prop) (by repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))]
  let f := fun a b c d r s => W 0 (r,a) * W 1 (a,b) * W 2 (b,s) *
    W 3 (s,c) * W 4 (c,d) * W 5 (d,r)
  change (∫ a, ∫ b, ∫ c, ∫ d, ∫ r, ∫ s, f a b c d r s ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ) = _
  calc
    _ = ∫ a, ∫ b, ∫ c, ∫ r, ∫ d, ∫ s, f a b c d r s ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro b
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro c
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ a, ∫ b, ∫ r, ∫ c, ∫ d, ∫ s, f a b c d r s ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro b
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ a, ∫ r, ∫ b, ∫ c, ∫ d, ∫ s, f a b c d r s ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ r, ∫ a, ∫ b, ∫ c, ∫ d, ∫ s, f a b c d r s ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ r, ∫ a, ∫ b, ∫ c, ∫ s, ∫ d, f a b c d r s ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro b
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro c
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = ∫ r, ∫ a, ∫ b, ∫ s, ∫ c, ∫ d, f a b c d r s ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro b
      exact integral_integral_swap (LowSupportAnalysis.unit_integrable
        (by dsimp [f]; fun_prop) (by dsimp [f]; repeat' first | exact hb _ _ | apply LowSupportAnalysis.mul_unit | apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro p))
    _ = LowSupportCycle.cycleNested (μ := μ) W := by rfl

lemma bowtie_congr_ae (W V : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hV : ∀ i, Measurable (V i))
    (he : ∀ i, W i =ᵐ[μ.prod μ] V i) : bowtie μ W = bowtie μ V := by
  have hr i := Measure.ae_ae_of_ae_prod (he i)
  have hv i : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, W i (x,y) = V i (x,y) :=
    (Measure.ae_ae_comm (p := fun x y => W i (x,y) = V i (x,y))
      (measurableSet_eq_fun (hW i) (hV i))).mp (hr i)
  unfold bowtie outerMeasure
  apply integral_congr_ae
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [hv 0, hr 1] with a ha0 ha1
      filter_upwards [ha1, hr 2] with b hab hb2
      apply (Measure.ae_prod_iff_ae_ae ?_).mpr
      · filter_upwards [hv 3, hr 4] with c hc3 hc4
        filter_upwards [hc4, hr 5] with d hcd hd5
        unfold outerEdges
        rw [hab,hcd]
        congr 1
        apply integral_congr_ae
        filter_upwards [ha0,hb2,hc3,hd5] with r h0 h2 h3 h5
        simp only [leftSpokes,rightSpokes,h0,h2,h3,h5]
      · apply measurableSet_eq_fun <;> dsimp [outerEdges,leftSpokes,rightSpokes] <;> fun_prop
    · simp only [ae_iff]
      apply measurableSet_eq_fun
      · change Measurable (fun x => (μ.prod μ) (Prod.mk x ⁻¹'
          {p : Outer Ω | ¬ outerEdges W p * (∫ r, leftSpokes W (r,p) * rightSpokes W (r,p) ∂μ) =
            outerEdges V p * (∫ r, leftSpokes V (r,p) * rightSpokes V (r,p) ∂μ)}))
        apply measurable_measure_prodMk_left
        apply MeasurableSet.compl
        apply measurableSet_eq_fun <;> dsimp [outerEdges,leftSpokes,rightSpokes] <;> fun_prop
      · exact measurable_const
  · apply measurableSet_eq_fun <;> dsimp [outerEdges,leftSpokes,rightSpokes] <;> fun_prop

lemma bowtie_sq_le_cycle_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1) :
    (bowtie μ W)^2 ≤ LowSupportCycle.cycleNested (μ := μ) W := by
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
  rw [bowtie_congr_ae μ W V hW hV he,
    LowSupportCycle.cycleNested_congr_ae W V hW hV he, ← cycle_eq_nested μ V hV bV]
  exact bowtie_sq_le_cycle μ V hV bV
lemma canonical_cycle_pos_of_bowtie_pos_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hpos : 0 < bowtie μ W) : 0 < LowSupportCycle.cycleNested (μ := μ) W := by
  have hs := bowtie_sq_le_cycle_ae μ W hW hb
  nlinarith [sq_pos_of_pos hpos]

lemma bowtie_zero_of_canonical_cycle_zero_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (hb : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W = 0) : bowtie μ W = 0 := by
  have hs := bowtie_sq_le_cycle_ae μ W hW hb
  rw [hz] at hs
  nlinarith [sq_nonneg (bowtie μ W)]
end RootedBowtie
end JigBundleModule144

/- Inlined module ThirdsRestrictedBowtie; original SHA256 c8fa5bdc82c8e83ef856ab32d035a23197bf3f853e1f28da351650f5ba7ddf14 -/
section JigBundleModule145
open MeasureTheory
namespace ThirdsRestrictedBowtie
open RootedBowtie
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma rooted_zero (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (hz : bowtie μ W = 0) :
    ∀ᵐ r ∂μ, ∀ᵐ a ∂μ, ∀ᵐ b ∂μ, ∀ᵐ c ∂μ, ∀ᵐ d ∂μ,
      W 0 (r,a)*W 1 (a,b)*W 2 (b,r)*W 3 (r,c)*W 4 (c,d)*W 5 (d,r)=0 := by
  have ho : ∀ᵐ p ∂outerMeasure μ, ∀ᵐ r ∂μ,
      outerEdges W p * (leftSpokes W (r,p)*rightSpokes W (r,p))=0 := by
    have hz' : (∫ p, outerEdges W p * (∫ r, leftSpokes W (r,p)*rightSpokes W (r,p) ∂μ) ∂outerMeasure μ)=0 := hz
    have hh := (TwoPairDoubledDisjoint.unit_zero_iff (outerMeasure μ) _
      (by unfold outerEdges leftSpokes rightSpokes; fun_prop) (by
        intro p
        unfold outerEdges leftSpokes rightSpokes
        repeat' first | exact bW _ _ | apply LowSupportAnalysis.mul_unit |
          apply LowSupportAnalysis.integral_unit_bounds | fun_prop | intro q)).mp hz'
    filter_upwards [hh] with p hp
    rw [← integral_const_mul] at hp
    exact (TwoPairDoubledDisjoint.unit_zero_iff μ _
      (by unfold outerEdges leftSpokes rightSpokes; fun_prop) (by
        intro r
        unfold outerEdges leftSpokes rightSpokes
        repeat' first | exact bW _ _ | apply LowSupportAnalysis.mul_unit)).mp hp
  have hr := (Measure.ae_ae_comm (p := fun p r =>
      outerEdges W p * (leftSpokes W (r,p)*rightSpokes W (r,p))=0)
      (by
        apply measurableSet_eq_fun
        · dsimp [outerEdges,leftSpokes,rightSpokes]; fun_prop
        · exact measurable_const)).mp ho
  filter_upwards [hr] with r hr
  have h1 := Measure.ae_ae_of_ae_prod hr
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with a ha
  filter_upwards [ha] with b hb
  have h3 := Measure.ae_ae_of_ae_prod hb
  filter_upwards [h3] with c hc
  filter_upwards [hc] with d hd
  dsimp [outerEdges,leftSpokes,rightSpokes] at hd
  nlinarith only [hd]

lemma five_full (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (bW : ∀ i p, 0 ≤ W i p ∧ W i p ≤ 1)
    (Z K X H Y : Set Ω) (pZ : μ Z ≠ 0) (pK : μ K ≠ 0) (pX : μ X ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈K → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈K → p.2∈X → W 1 p=1)
    (f2 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Z → W 2 p=1)
    (f3 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → W 3 p=1)
    (f5 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈Z → W 5 p=1)
    (hz : bowtie μ W = 0) :
    ∀ᵐ c ∂μ, c∈H → ∀ᵐ d ∂μ, d∈Y → W 4 (c,d)=0 := by
  have h0 := Measure.ae_ae_of_ae_prod f0
  have h1 := Measure.ae_ae_of_ae_prod f1
  have h2 := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae f2)
  have h3 := Measure.ae_ae_of_ae_prod f3
  have h5 := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae f5)
  have hg := rooted_zero μ W hW bW hz
  have good := hg.and (h0.and (h2.and (h3.and h5)))
  obtain ⟨r,hrZ,hr,h0r,h2r,h3r,h5r⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pZ (ae_restrict_of_ae good)
  have gooda := hr.and (h0r.and h1)
  obtain ⟨a,haK,ha,h0a,h1a⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pK (ae_restrict_of_ae gooda)
  have goodb := ha.and (h1a.and h2r)
  obtain ⟨b,hbX,hb,h1b,h2b⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pX (ae_restrict_of_ae goodb)
  filter_upwards [hb,h3r] with c hc h3c
  intro hcH
  filter_upwards [hc,h5r] with d hd h5d
  intro hdY
  have e2 : W 2 (b,r)=1 := h2b hbX hrZ
  have e5 : W 5 (d,r)=1 := h5d hdY hrZ
  simpa [h0a hrZ haK,h1b haK hbX,e2,h3c hrZ hcH,e5] using hd

lemma five_full_ae (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (bW : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (Z K X H Y : Set Ω) (pZ : μ Z ≠ 0) (pK : μ K ≠ 0) (pX : μ X ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈K → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈K → p.2∈X → W 1 p=1)
    (f2 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Z → W 2 p=1)
    (f3 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → W 3 p=1)
    (f5 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈Z → W 5 p=1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W = 0) :
    ∀ᵐ c ∂μ, c∈H → ∀ᵐ d ∂μ, d∈Y → W 4 (c,d)=0 := by
  let V : Fin 6 → Ω × Ω → ℝ := fun i p => max 0 (min 1 (W i p))
  have hV : ∀ i, Measurable (V i) := by intro i; dsimp [V]; fun_prop
  have bV : ∀ i p, 0 ≤ V i p ∧ V i p ≤ 1 := by
    intro i p
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have he : ∀ i, W i =ᵐ[μ.prod μ] V i := by
    intro i
    filter_upwards [bW i] with p hp
    dsimp [V]
    rw [min_eq_right hp.2,max_eq_right hp.1]
  have hzV : bowtie μ V=0 := by
    rw [← RootedBowtie.bowtie_congr_ae μ W V hW hV he]
    exact RootedBowtie.bowtie_zero_of_canonical_cycle_zero_ae μ W hW bW hz
  have transfer (i : Fin 6) (S T : Set Ω)
      (hf : ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈T → W i p=1) :
      ∀ᵐ p ∂μ.prod μ, p.1∈S → p.2∈T → V i p=1 := by
    filter_upwards [hf,he i] with p hp ep
    simpa only [← ep] using hp
  have hh := five_full μ V hV bV Z K X H Y pZ pK pX
    (transfer 0 Z K f0) (transfer 1 K X f1) (transfer 2 X Z f2)
    (transfer 3 Z H f3) (transfer 5 Y Z f5) hzV
  filter_upwards [hh,Measure.ae_ae_of_ae_prod (he 4)] with c hc ec
  intro hcH
  filter_upwards [hc hcH,ec] with d hd ed
  intro hdY
  rw [ed]
  exact hd hdY

lemma candidate_null (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ i, Measurable (W i))
    (bW : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ W i p ∧ W i p ≤ 1)
    (Z K X H Y : Set Ω) (hH : MeasurableSet H) (hY : MeasurableSet Y)
    (pZ : μ Z ≠ 0) (pX : μ X ≠ 0)
    (f0 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈K → W 0 p=1)
    (f1 : ∀ᵐ p ∂μ.prod μ, p.1∈K → p.2∈X → W 1 p=1)
    (f2 : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈Z → W 2 p=1)
    (f3 : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → W 3 p=1)
    (f5 : ∀ᵐ p ∂μ.prod μ, p.1∈Y → p.2∈Z → W 5 p=1)
    (hz : LowSupportCycle.cycleNested (μ := μ) W = 0)
    (hpos : 0 < ∫ c in H, ∫ d in Y, W 4 (c,d) ∂μ ∂μ) : μ K=0 := by
  by_contra pK
  have hh := five_full_ae μ W hW bW Z K X H Y pZ pK pX f0 f1 f2 f3 f5 hz
  have hi : (∫ c in H, ∫ d in Y, W 4 (c,d) ∂μ ∂μ)=0 := by
    have ho : ∀ᵐ c ∂μ.restrict H, (∫ d in Y, W 4 (c,d) ∂μ)=0 := by
      apply (ae_restrict_iff' hH).mpr
      filter_upwards [hh] with c hc
      intro hcH
      rw [integral_congr_ae ((ae_restrict_iff' hY).mpr (hc hcH)),integral_zero]
    rw [integral_congr_ae ho,integral_zero]
  linarith

end ThirdsRestrictedBowtie
end JigBundleModule145

/- Inlined module ThirdsOneMixingContainment; original SHA256 369535643f614ca75031857be07b02f9be01cc4214adf2a3a90e1fc2fa644158 -/
section JigBundleModule146
open MeasureTheory
namespace ThirdsOneMixingContainment
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- a,b,c,D,E,F are numbered 0,1,2,3,4,5. -/
def order (i : Fin 4) : Fin 6 → Fin 6 :=
  ![![0,3,2,5,4,1], ![0,4,2,5,3,1], ![0,3,1,5,4,2], ![0,4,1,5,3,2]] i

noncomputable def permutation (i : Fin 4) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (order i) (by fin_cases i <;> decide)

lemma order_zero (i : Fin 4) : order i 0=0 := by fin_cases i <;> rfl

lemma candidate_classes_null (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0)
    (Z Ra H : Set Ω) (C T U : Fin 4 → Set Ω)
    (hH : MeasurableSet H) (hU : ∀ i, MeasurableSet (U i))
    (pZ : μ Z ≠ 0) (pT : ∀ i, μ (T i) ≠ 0)
    (fa : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈Ra → W 0 p=1)
    (f1 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈Ra∩C i → p.2∈T i → W (order i 1) p=1)
    (f2 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈T i → p.2∈Z → W (order i 2) p=1)
    (f3 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → W (order i 3) p=1)
    (f5 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈U i → p.2∈Z → W (order i 5) p=1)
    (hp : ∀ i, 0 < ∫ h in H, ∫ u in U i, W (order i 4) (h,u) ∂μ ∂μ) :
    ∀ i, μ (Ra∩C i)=0 := by
  intro i
  apply ThirdsRestrictedBowtie.candidate_null μ (fun c => W (order i c))
    (fun c => hW (order i c)) (fun c => bW (order i c))
    Z (Ra∩C i) (T i) H (U i) hH (hU i) pZ (pT i)
  · filter_upwards [fa] with p hf
    intro hpZ hpK
    simpa only [order_zero] using hf hpZ hpK.1
  · exact f1 i
  · exact f2 i
  · exact f3 i
  · exact f5 i
  · exact hz (permutation i)
  · exact hp i

lemma full_zero_intersection (A : Ω × Ω → ℝ) (Z Ra H : Set Ω) (pZ : μ Z ≠ 0)
    (hf : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈Ra → A p=1)
    (hz : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → A p=0) : μ (Ra∩H)=0 := by
  have good := (Measure.ae_ae_of_ae_prod hf).and (Measure.ae_ae_of_ae_prod hz)
  obtain ⟨z,hzZ,hf,hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pZ (ae_restrict_of_ae good)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf,hz] with r hf hz
  intro hr
  have h1 := hf hzZ hr.1
  have h0 := hz hzZ hr.2
  linarith

lemma mass_of_coverage (Z Ra H : Set Ω) (C : Fin 4 → Set Ω)
    (hH : μ (Ra∩H)=0) (hC : ∀ i, μ (Ra∩C i)=0)
    (hc : ∀ᵐ r ∂μ, r∈Ra → r∈Z ∨ r∈H ∨ ∃ i, r∈C i)
    (d : ℝ) (mRa : μ.real Ra=d) (mZ : μ.real Z≤d) : μ.real Z=d := by
  have hnH := measure_eq_zero_iff_ae_notMem.mp hH
  have hnC : ∀ᵐ r ∂μ, ∀ i, r∉Ra∩C i := ae_all_iff.mpr (fun i => measure_eq_zero_iff_ae_notMem.mp (hC i))
  have hsub : Ra ≤ᵐ[μ] Z := by
    filter_upwards [hc,hnH,hnC] with r hr hH hC
    intro hRa
    rcases hr hRa with hZ | hH' | ⟨i,hi⟩
    · exact hZ
    · exact (hH ⟨hRa,hH'⟩).elim
    · exact (hC i ⟨hRa,hi⟩).elim
  have hm : μ.real Ra ≤ μ.real Z := ENNReal.toReal_mono (measure_ne_top μ Z) (measure_mono_ae hsub)
  linarith

lemma containment_mass (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0)
    (Z Ra H : Set Ω) (C T U : Fin 4 → Set Ω)
    (hH : MeasurableSet H) (hU : ∀ i, MeasurableSet (U i))
    (pZ : μ Z ≠ 0) (pT : ∀ i, μ (T i) ≠ 0)
    (fa : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈Ra → W 0 p=1)
    (fH : ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → W 0 p=0)
    (f1 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈Ra∩C i → p.2∈T i → W (order i 1) p=1)
    (f2 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈T i → p.2∈Z → W (order i 2) p=1)
    (f3 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈Z → p.2∈H → W (order i 3) p=1)
    (f5 : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1∈U i → p.2∈Z → W (order i 5) p=1)
    (hp : ∀ i, 0 < ∫ h in H, ∫ u in U i, W (order i 4) (h,u) ∂μ ∂μ)
    (hc : ∀ᵐ r ∂μ, r∈Ra → r∈Z ∨ r∈H ∨ ∃ i, r∈C i)
    (d : ℝ) (mRa : μ.real Ra=d) (mZ : μ.real Z≤d) : μ.real Z=d := by
  exact mass_of_coverage μ Z Ra H C (full_zero_intersection μ (W 0) Z Ra H pZ fa fH)
    (candidate_classes_null μ W hW bW hz Z Ra H C T U hH hU pZ pT fa f1 f2 f3 f5 hp)
    hc d mRa mZ

end ThirdsOneMixingContainment
end JigBundleModule146

/- Inlined module ThirdsPairCover; original SHA256 a3a14f7076d472236c9bd035f4a4ea4c72a4b56b0f8a8d5e239b337b6b7f32a6 -/
section JigBundleModule147
open MeasureTheory
namespace ThirdsPairCover
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma pair_cover (T : Fin 6 → Set Ω) (S : Set Ω)
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S)
    (hc : ∀ᵐ x ∂μ, ∑ c, oneSet (T c) x=2) :
    ∀ᵐ x ∂μ, x∉S → x∉T 1∩T 5 → x∉T 2∩T 5 → x∉T 3∩T 5 → x∉T 4∩T 5 →
      x∈T 1∩T 2 ∨ x∈T 3∩T 4 ∨ x∈T 1∩T 3 ∨ x∈T 1∩T 4 ∨ x∈T 2∩T 3 ∨ x∈T 2∩T 4 := by
  filter_upwards [h0,hc] with x hx hcount
  intro hs h15 h25 h35 h45
  have e0 : oneSet (T 0) x=0 := by rw [hx]; simp [oneSet,hs]
  classical
  by_cases h1 : x∈T 1 <;> by_cases h2 : x∈T 2 <;> by_cases h3 : x∈T 3 <;>
    by_cases h4 : x∈T 4 <;> by_cases h5 : x∈T 5 <;>
    simp_all [Fin.sum_univ_six,oneSet]
end ThirdsPairCover
end JigBundleModule147

/- Inlined module ThirdsOneMixingContainmentActual; original SHA256 5b33db143f4cf28a460032b68e6fb0f1c68bdc80b89ce53c2123469935a9c479 -/
section JigBundleModule148
open MeasureTheory
namespace ThirdsOneMixingContainmentActual
open FourColorKernels TwoPairHalfSetOperator ThirdsSelectedCenter
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- An outside vertex active in a clique color and a second color is full in
that second color towards the original clique. -/
lemma outside_partner_full (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0<d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω)
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (i j : Fin 6) (hij : i≠j)
    (hcl : ∀ᵐ p ∂μ.prod μ, p.1∈X → W i p=oneSet X p.2) :
    ∀ᵐ u ∂μ, u∉S → u∈T i∩T j → (fun x => W j (u,x)) =ᵐ[μ] oneSet X := by
  let ν := ProbabilityTheory.cond μ S
  have hac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hi := ThirdsCaseBFullRows.outside_active_full_other μ (W i) (hW i) (bW i) (sW i)
    S X (T i) hS hX hXS d hd mS mX (hr i) hcl (hf i)
  have ey : oneSet (S\X) =ᵐ[ν] (fun x => 1-oneSet X x) := by
    apply ThirdsNormalizedRestriction.conditional_ae μ S hS
    exact Filter.Eventually.of_forall (fun x hx => by by_cases hxx : x∈X <;> simp [oneSet,hx,hxx])
  filter_upwards [hi,rowGood_ae μ W bW sW hpart,ae_all_iff.mpr hf,hr j] with u hui hu hfu hru
  intro hus hut
  have mass (c : Fin 6) (hc : u∈T c) : act μ (W c) (oneSet S) u=d := by
    rw [hfu c]; simp [oneSet,hc]
  obtain ⟨r,hrm,br,mr,er,eg,_⟩ := selected_center μ W hW S hS d hd mS u hu i j hij
    (mass i hut.1) (mass j hut.2)
  have he : (fun x => W j (u,x)) =ᵐ[ν] oneSet X := by
    have hbi := ((hui hus hut.1).filter_mono hac.ae_le).trans ey
    filter_upwards [er,eg,hbi] with x hx hy hb
    change W i (u,x)=(1+r x)/2 at hx
    change W j (u,x)=(1-r x)/2 at hy
    linarith
  exact ThirdsFullTargetRow.extend μ (fun x => W j (u,x)) (by fun_prop)
    ((hu.1 j).mono (fun _ h => ⟨h.1,h.2.1⟩)) S X hS hX hXS d hru mX he
lemma mass_eq (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0)
    (Ra : Set Ω) (hRa : MeasurableSet Ra)
    (subRa : Ra⊆Sᶜ\(((T 3∩T 5)\S)∪((T 4∩T 5)\S))) (mRa : μ.real Ra=d)
    (fa : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W 0 p=oneSet Ra p.2)
    (fH : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 4)\S → W 0 p=0)
    (ff : ∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → p.2∈(T 3∩T 4)\S → W 5 p=1)
    (p3X : 0<∫ h in (T 3∩T 4)\S, ∫ x in X, W 3 (h,x) ∂μ ∂μ)
    (p4X : 0<∫ h in (T 3∩T 4)\S, ∫ x in X, W 4 (h,x) ∂μ ∂μ)
    (p3Y : 0<∫ h in (T 3∩T 4)\S, ∫ x in S\X, W 3 (h,x) ∂μ ∂μ)
    (p4Y : 0<∫ h in (T 3∩T 4)\S, ∫ x in S\X, W 4 (h,x) ∂μ ∂μ) :
    μ.real ((T 1∩T 2)\S)=d := by
  classical
  obtain ⟨pZ,mH,mI,mJ,fb,fc,fd,fe⟩ := ThirdsOneMixingFourTargets.four_targets
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  obtain ⟨_,_,_,_,n15,n25,_,_⟩ := ThirdsCaseBActualMasses.mixing_mass_structure
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  have hY : MeasurableSet (S\X) := hS.diff hX
  have mY : μ.real (S\X)=d := by rw [measureReal_sdiff hXS hX,mS,mX]; ring
  have pX : μ X≠0 := by intro he; simp [measureReal_def,he] at mX; linarith
  have pY : μ (S\X)≠0 := by intro he; simp [measureReal_def,he] at mY; linarith
  have pZ' : μ ((T 1∩T 2)\S)≠0 := by
    intro he
    change 0<μ.real ((T 1∩T 2)\S) at pZ
    simp [measureReal_def,he] at pZ
  have mZ : μ.real ((T 1∩T 2)\S)≤d := by
    obtain ⟨r1,_,_,_,_⟩ := ThirdsCaseBMassAssembly.mass_setup μ T S hT hS d hm h0 hc mb mc mD mE mF
    have n13 := ThirdsCaseBMassAssembly.nonneg μ T S 1 3
    have n14 := ThirdsCaseBMassAssembly.nonneg μ T S 1 4
    have n15 := ThirdsCaseBMassAssembly.nonneg μ T S 1 5
    change ThirdsCaseBMassAssembly.pairMass μ T S 1 2≤d
    linarith
  have outRa : ∀ x∈Ra, x∉S := fun x hx => (subRa hx).1
  have r13 := outside_partner_full μ W hW bW sW hpart S X hS hX hXS
    d hd mS mX hr T hf 1 3 (by decide) hcl1
  have r14 := outside_partner_full μ W hW bW sW hpart S X hS hX hXS
    d hd mS mX hr T hf 1 4 (by decide) hcl1
  have r23 := outside_partner_full μ W hW bW sW hpart S (S\X) hS hY Set.sdiff_subset
    d hd mS mY hr T hf 2 3 (by decide) hcl2
  have r24 := outside_partner_full μ W hW bW sW hpart S (S\X) hS hY Set.sdiff_subset
    d hd mS mY hr T hf 2 4 (by decide) hcl2
  have f13 : ∀ᵐ p ∂μ.prod μ, p.1∈Ra∩(T 1∩T 3) → p.2∈X → W 3 p=1 := by
    apply ThirdsOneMixingATarget.rectangle_of_rows μ (W 3) (hW 3)
      (Ra∩(T 1∩T 3)) X (hRa.inter ((hT 1).inter (hT 3))) hX
    filter_upwards [r13] with u hu
    intro hh
    exact hu (outRa u hh.1) hh.2
  have f14 : ∀ᵐ p ∂μ.prod μ, p.1∈Ra∩(T 1∩T 4) → p.2∈X → W 4 p=1 := by
    apply ThirdsOneMixingATarget.rectangle_of_rows μ (W 4) (hW 4)
      (Ra∩(T 1∩T 4)) X (hRa.inter ((hT 1).inter (hT 4))) hX
    filter_upwards [r14] with u hu
    intro hh
    exact hu (outRa u hh.1) hh.2
  have f23 : ∀ᵐ p ∂μ.prod μ, p.1∈Ra∩(T 2∩T 3) → p.2∈(S\X) → W 3 p=1 := by
    apply ThirdsOneMixingATarget.rectangle_of_rows μ (W 3) (hW 3)
      (Ra∩(T 2∩T 3)) (S\X) (hRa.inter ((hT 2).inter (hT 3))) hY
    filter_upwards [r23] with u hu
    intro hh
    exact hu (outRa u hh.1) hh.2
  have f24 : ∀ᵐ p ∂μ.prod μ, p.1∈Ra∩(T 2∩T 4) → p.2∈(S\X) → W 4 p=1 := by
    apply ThirdsOneMixingATarget.rectangle_of_rows μ (W 4) (hW 4)
      (Ra∩(T 2∩T 4)) (S\X) (hRa.inter ((hT 2).inter (hT 4))) hY
    filter_upwards [r24] with u hu
    intro hh
    exact hu (outRa u hh.1) hh.2
  have rb : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → p.2∈(T 1∩T 2)\S → W 1 p=1 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae fb,sW 1] with p hp hs
    intro hy hz
    rw [hs]
    simpa [Prod.swap,oneSet,hy] using hp hz
  have rc : ∀ᵐ p ∂μ.prod μ, p.1∈X → p.2∈(T 1∩T 2)\S → W 2 p=1 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae fc,sW 2] with p hp hs
    intro hx hz
    rw [hs]
    simpa [Prod.swap,oneSet,hx] using hp hz
  let C : Fin 4 → Set Ω := ![T 1∩T 3,T 1∩T 4,T 2∩T 3,T 2∩T 4]
  let K : Fin 4 → Set Ω := ![X,X,S\X,S\X]
  let U : Fin 4 → Set Ω := ![S\X,S\X,X,X]
  have cover : ∀ᵐ r ∂μ, r∈Ra → r∈(T 1∩T 2)\S ∨ r∈(T 3∩T 4)\S ∨ ∃ i, r∈C i := by
    filter_upwards [ThirdsPairCover.pair_cover μ T S h0 hc,
      measure_eq_zero_iff_ae_notMem.mp n15,measure_eq_zero_iff_ae_notMem.mp n25] with r hh h15 h25
    intro hra
    have hs := outRa r hra
    have hi : r∉T 3∩T 5 := fun ht => (subRa hra).2 (Or.inl ⟨ht,hs⟩)
    have hj : r∉T 4∩T 5 := fun ht => (subRa hra).2 (Or.inr ⟨ht,hs⟩)
    rcases hh hs h15 h25 hi hj with h12|h34|h13|h14|h23|h24
    · exact Or.inl ⟨h12,hs⟩
    · exact Or.inr (Or.inl ⟨h34,hs⟩)
    · exact Or.inr (Or.inr ⟨0,h13⟩)
    · exact Or.inr (Or.inr ⟨1,h14⟩)
    · exact Or.inr (Or.inr ⟨2,h23⟩)
    · exact Or.inr (Or.inr ⟨3,h24⟩)
  apply ThirdsOneMixingContainment.containment_mass μ W hW bW hz
    ((T 1∩T 2)\S) Ra ((T 3∩T 4)\S) C K U (((hT 3).inter (hT 4)).diff hS)
    (by intro i; fin_cases i <;> simp only [U] <;> assumption)
    pZ' (by intro i; fin_cases i <;> simp only [K] <;> assumption)
    _ fH _ _ _ _ _ cover d mRa mZ
  · filter_upwards [fa] with p hp
    intro hz hr; simpa [oneSet,hr] using hp hz
  · intro i
    fin_cases i
    · simpa [C,K,ThirdsOneMixingContainment.order] using f13
    · simpa [C,K,ThirdsOneMixingContainment.order] using f14
    · simpa [C,K,ThirdsOneMixingContainment.order] using f23
    · simpa [C,K,ThirdsOneMixingContainment.order] using f24
  · intro i
    fin_cases i <;> simp only [K,ThirdsOneMixingContainment.order] <;> assumption
  · intro i
    fin_cases i <;> simpa [ThirdsOneMixingContainment.order] using ff
  · intro i
    fin_cases i <;> simp only [U,ThirdsOneMixingContainment.order] <;> assumption
  · intro i
    fin_cases i <;> simp only [U,ThirdsOneMixingContainment.order] <;> assumption
end ThirdsOneMixingContainmentActual
end JigBundleModule148

/- Inlined module ThirdsCaseBOneMixing; original SHA256 09316a08840d6b6f7386386b6f61666346ffa7fa5ba87130dacb616953f7a403 -/
section JigBundleModule149
open MeasureTheory
namespace ThirdsCaseBOneMixing
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly ThirdsCaseBNoMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma one_mixing_twin (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T 3∩T 4 →
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W 3 (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0)
    (ha35 : ∀ᵐ u ∂μ, u∈T 3∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 3 (u,x)) X)
    (ha45 : ∀ᵐ u ∂μ, u∈T 4∩T 5 → Aligned (ProbabilityTheory.cond μ S) (fun x => W 4 (u,x)) X) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
  obtain ⟨Ra,hRa,subRa,mRa,fa⟩ := ThirdsOneMixingATarget.a_target
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF ha35
  have fH := ThirdsOneMixingActualHZero.h_zero
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF ha35 ha45
  obtain ⟨_,_,_,_,f1,f2,f3,f4⟩ := ThirdsOneMixingFourTargets.four_targets
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF
  have res := ThirdsFourTargetsResidual.residual μ W (fun c => (bW c).mono fun _ h => h.1)
    hpart S X ((T 1∩T 2)\S) ((T 3∩T 5)\S) ((T 4∩T 5)\S) hXS f1 f2 f3 f4
  have ff := ThirdsOneMixingFullF.full_f_on_h μ W T hT S hc res.1 fH
  obtain ⟨p3X,p4X,p3Y,p4Y⟩ := ThirdsOneMixingActualPositive.four_positive
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX T hT hf hn mD
  have mZ := ThirdsOneMixingContainmentActual.mass_eq
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF Ra hRa subRa mRa fa fH ff p3X p4X p3Y p4Y
  exact ThirdsOneMixingTwin.twin_of_mass
    μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
    hcl1 hcl2 haX haY hz hn hm mb mc mD mE mF ha35 mZ
end ThirdsCaseBOneMixing
end JigBundleModule149

/- Inlined module ThirdsCaseBAllMixing; original SHA256 e56220334b7ff9aab0e4c07a9bee9bcc9d68dba2c68681565d715abe45f4ea2b -/
section JigBundleModule150
open MeasureTheory
namespace ThirdsCaseBAllMixing
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly ThirdsCaseBNoMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
def Mixing (W : Fin 6 → Ω×Ω → ℝ) (S X : Set Ω) (T : Fin 6 → Set Ω) (i j : Fin 6) : Prop :=
  ¬ (∀ᵐ u ∂μ, u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X)
lemma permuted_two_mixing_twin (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (σ : Equiv.Perm (Fin 6)) (s0 : σ 0=0) (s1 : σ 1=1) (s2 : σ 2=2)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T (σ 3)∩T (σ 4) →
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hn35 : ¬ (∀ᵐ u ∂μ, u∈T (σ 3)∩T (σ 5) →
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have count : ∀ᵐ u ∂μ, ∑ c, oneSet (T (σ c)) u=2 := by
    filter_upwards [hc] with u hu
    rw [Equiv.sum_comp σ (fun c => oneSet (T c) u)]; exact hu
  have cycles : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have vm (c : Fin 6) (h0 : c≠0) (h1 : c≠1) (h2 : c≠2) : μ.real (S∩T c)=0 := by
    fin_cases c
    · exact (h0 rfl).elim
    · exact (h1 rfl).elim
    · exact (h2 rfl).elim
    · exact mD
    · exact mE
    · exact mF
  have ne (i j : Fin 6) (hij : i≠j) (sj : σ j=j) : σ i≠j :=
    fun h => hij (σ.injective (h.trans sj.symm))
  have mz (i : Fin 6) (i0 : i≠0) (i1 : i≠1) (i2 : i≠2) : μ.real (S∩T (σ i))=0 :=
    vm (σ i) (ne i 0 i0 s0) (ne i 1 i1 s1) (ne i 2 i2 s2)
  obtain ⟨mZ,targets⟩ := ThirdsCaseBTwoMixing.two_mixing_twin μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) part S X hS hX hXS d hd mS mX
    (fun c => hr (σ c)) (fun c => T (σ c)) (fun c => hT (σ c)) (fun c => hf (σ c))
    (by simpa only [s0] using h0) count (by simpa only [s1] using hcl1) (by simpa only [s2] using hcl2)
    (by simpa only [s0] using haX) (by simpa only [s0] using haY) cycles hn hn35 (fun c => hm (σ c))
    (by simpa only [s1] using mb) (by simpa only [s2] using mc)
    (mz 3 (by decide) (by decide) (by decide)) (mz 4 (by decide) (by decide) (by decide)) (mz 5 (by decide) (by decide) (by decide))
  refine ⟨?_,?_⟩
  · simpa only [pairMass,s1,s2] using mZ
  · intro c
    simpa only [σ.apply_symm_apply,s1,s2] using targets (σ.symm c)
lemma at_least_two_mixing_twin (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hmix : (Mixing μ W S X T 3 4 ∧ Mixing μ W S X T 3 5) ∨
      (Mixing μ W S X T 3 4 ∧ Mixing μ W S X T 4 5) ∨
      (Mixing μ W S X T 3 5 ∧ Mixing μ W S X T 4 5))
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
  have reverse (i j : Fin 6) (hij : i≠j) (h : Mixing μ W S X T i j) : Mixing μ W S X T j i :=
    ThirdsMixingRelabel.mixing_reverse μ W hW S X hS d hd mS T
      (ThirdsSelectedCenter.rowGood_ae μ W bW sW hpart) hf i j hij h
  have run (σ : Equiv.Perm (Fin 6)) (s0 : σ 0=0) (s1 : σ 1=1) (s2 : σ 2=2)
      (a : Mixing μ W S X T (σ 3) (σ 4)) (b : Mixing μ W S X T (σ 3) (σ 5)) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) :=
    permuted_two_mixing_twin μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
      hcl1 hcl2 haX haY hz σ s0 s1 s2 a b hm mb mc mD mE mF
  rcases hmix with ⟨h34,h35⟩ | ⟨h34,h45⟩ | ⟨h35,h45⟩
  · exact run (Equiv.refl _) rfl rfl rfl h34 h35
  · let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,1,2,4,3,5] (by decide)
    exact run σ rfl rfl rfl (reverse 3 4 (by decide) h34) h45
  · let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,1,2,5,3,4] (by decide)
    exact run σ rfl rfl rfl (reverse 3 5 (by decide) h35) (reverse 4 5 (by decide) h45)
end ThirdsCaseBAllMixing
end JigBundleModule150

/- Inlined module ThirdsCaseBComplete; original SHA256 046110e4b6b5e918feab14a7bb3f638848ca9ce15cc8867ed0e30f7be62ab2bc -/
section JigBundleModule151
open MeasureTheory
namespace ThirdsCaseBComplete
open FourColorKernels TwoPairHalfSetOperator ThirdsCaseBMassAssembly ThirdsCaseBNoMixing ThirdsCaseBAllMixing
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma permuted_one_mixing_twin (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (σ : Equiv.Perm (Fin 6)) (s0 : σ 0=0) (s1 : σ 1=1) (s2 : σ 2=2)
    (hn : ¬ (∀ᵐ u ∂μ, u∈T (σ 3)∩T (σ 4) →
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] oneSet X) ∨
      ((fun x => W (σ 3) (u,x)) =ᵐ[ProbabilityTheory.cond μ S] (fun x => 1-oneSet X x))))
    (ha35 : ∀ᵐ u ∂μ, u∈T (σ 3)∩T (σ 5) → Aligned (ProbabilityTheory.cond μ S) (fun x => W (σ 3) (u,x)) X)
    (ha45 : ∀ᵐ u ∂μ, u∈T (σ 4)∩T (σ 5) → Aligned (ProbabilityTheory.cond μ S) (fun x => W (σ 4) (u,x)) X)
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) := by
  have part : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have count : ∀ᵐ u ∂μ, ∑ c, oneSet (T (σ c)) u=2 := by
    filter_upwards [hc] with u hu
    rw [Equiv.sum_comp σ (fun c => oneSet (T c) u)]; exact hu
  have cycles : ∀ τ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ (τ i)))=0 := by
    intro τ; exact hz (τ.trans σ)
  have vm (c : Fin 6) (h0 : c≠0) (h1 : c≠1) (h2 : c≠2) : μ.real (S∩T c)=0 := by
    fin_cases c
    · exact (h0 rfl).elim
    · exact (h1 rfl).elim
    · exact (h2 rfl).elim
    · exact mD
    · exact mE
    · exact mF
  have ne (i j : Fin 6) (hij : i≠j) (sj : σ j=j) : σ i≠j :=
    fun h => hij (σ.injective (h.trans sj.symm))
  have mz (i : Fin 6) (i0 : i≠0) (i1 : i≠1) (i2 : i≠2) : μ.real (S∩T (σ i))=0 :=
    vm (σ i) (ne i 0 i0 s0) (ne i 1 i1 s1) (ne i 2 i2 s2)
  obtain ⟨mZ,targets⟩ := ThirdsCaseBOneMixing.one_mixing_twin μ (fun c => W (σ c)) (fun c => hW (σ c))
    (fun c => bW (σ c)) (fun c => sW (σ c)) part S X hS hX hXS d hd mS mX
    (fun c => hr (σ c)) (fun c => T (σ c)) (fun c => hT (σ c)) (fun c => hf (σ c))
    (by simpa only [s0] using h0) count (by simpa only [s1] using hcl1) (by simpa only [s2] using hcl2)
    (by simpa only [s0] using haX) (by simpa only [s0] using haY) cycles hn (fun c => hm (σ c))
    (by simpa only [s1] using mb) (by simpa only [s2] using mc)
    (mz 3 (by decide) (by decide) (by decide)) (mz 4 (by decide) (by decide) (by decide)) (mz 5 (by decide) (by decide) (by decide)) ha35 ha45
  refine ⟨?_,?_⟩
  · simpa only [pairMass,s1,s2] using mZ
  · intro c
    simpa only [σ.apply_symm_apply,s1,s2] using targets (σ.symm c)
lemma case_b_twin (W : Fin 6 → Ω × Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (S X : Set Ω) (hS : MeasurableSet S) (hX : MeasurableSet X) (hXS : X⊆S)
    (d : ℝ) (hd : 0 < d) (mS : μ.real S=2*d) (mX : μ.real X=d)
    (hr : ∀ c, ∀ᵐ u ∂μ, ∫ x, W c (u,x) ∂μ=d)
    (T : Fin 6 → Set Ω) (hT : ∀ c, MeasurableSet (T c))
    (hf : ∀ c, act μ (W c) (oneSet S) =ᵐ[μ] (fun u => d*oneSet (T c) u))
    (h0 : oneSet (T 0) =ᵐ[μ] oneSet S) (hc : ∀ᵐ u ∂μ, ∑ c, oneSet (T c) u=2)
    (hcl1 : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 1 p=oneSet X p.2)
    (hcl2 : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 2 p=oneSet (S\X) p.2)
    (haX : ∀ᵐ p ∂μ.prod μ, p.1∈X → W 0 p=oneSet (S\X) p.2)
    (haY : ∀ᵐ p ∂μ.prod μ, p.1∈S\X → W 0 p=oneSet X p.2)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun i => W (σ i))=0)
    (hm : ∀ c, μ.real (T c)=2*d)
    (mb : μ.real (S∩T 1)=d) (mc : μ.real (S∩T 2)=d)
    (mD : μ.real (S∩T 3)=0) (mE : μ.real (S∩T 4)=0) (mF : μ.real (S∩T 5)=0) :
    ∃ I : Set Ω, MeasurableSet I ∧ μ.real I=d ∧
      ∀ c, ∃ U : Set Ω, MeasurableSet U ∧ μ.real U=d ∧
        (∀ᵐ p ∂μ.prod μ, p.1∈I → W c p=oneSet U p.2) := by
  classical
  have out (h : pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
      MeasurableSet U ∧ μ.real U=d ∧
      (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2)) :
      ∃ I : Set Ω, MeasurableSet I ∧ μ.real I=d ∧
        ∀ c, ∃ U : Set Ω, MeasurableSet U ∧ μ.real U=d ∧
          (∀ᵐ p ∂μ.prod μ, p.1∈I → W c p=oneSet U p.2) :=
    ⟨(T 1∩T 2)\S,((hT 1).inter (hT 2)).diff hS,h.1,h.2⟩
  have reverse (i j : Fin 6) (hij : i≠j)
      (ha : ∀ᵐ u ∂μ, u∈T i∩T j → Aligned (ProbabilityTheory.cond μ S) (fun x => W i (u,x)) X) :
      ∀ᵐ u ∂μ, u∈T j∩T i → Aligned (ProbabilityTheory.cond μ S) (fun x => W j (u,x)) X :=
    ThirdsMixingRelabel.alignment_reverse μ W hW S X hS d hd mS T
      (ThirdsSelectedCenter.rowGood_ae μ W bW sW hpart) hf i j hij ha
  have run (σ : Equiv.Perm (Fin 6)) (s0 : σ 0=0) (s1 : σ 1=1) (s2 : σ 2=2)
      (hn : Mixing μ W S X T (σ 3) (σ 4))
      (ha35 : ∀ᵐ u ∂μ, u∈T (σ 3)∩T (σ 5) → Aligned (ProbabilityTheory.cond μ S) (fun x => W (σ 3) (u,x)) X)
      (ha45 : ∀ᵐ u ∂μ, u∈T (σ 4)∩T (σ 5) → Aligned (ProbabilityTheory.cond μ S) (fun x => W (σ 4) (u,x)) X) :
      pairMass μ T S 1 2=d ∧ ∀ c : Fin 6, ∃ U : Set Ω,
        MeasurableSet U ∧ μ.real U=d ∧
        (∀ᵐ p ∂μ.prod μ, p.1∈(T 1∩T 2)\S → W c p=oneSet U p.2) :=
    permuted_one_mixing_twin μ W hW bW sW hpart S X hS hX hXS d hd mS mX hr T hT hf h0 hc
      hcl1 hcl2 haX haY hz σ s0 s1 s2 hn ha35 ha45 hm mb mc mD mE mF
  by_cases hmany : (Mixing μ W S X T 3 4 ∧ Mixing μ W S X T 3 5) ∨
      (Mixing μ W S X T 3 4 ∧ Mixing μ W S X T 4 5) ∨
      (Mixing μ W S X T 3 5 ∧ Mixing μ W S X T 4 5)
  · exact out (ThirdsCaseBAllMixing.at_least_two_mixing_twin μ W hW bW sW hpart S X hS hX hXS
      d hd mS mX hr T hT hf h0 hc hcl1 hcl2 haX haY hz hmany hm mb mc mD mE mF)
  · by_cases h34 : Mixing μ W S X T 3 4
    · have h35 : ¬ Mixing μ W S X T 3 5 := fun h => hmany (Or.inl ⟨h34,h⟩)
      have h45 : ¬ Mixing μ W S X T 4 5 := fun h => hmany (Or.inr (Or.inl ⟨h34,h⟩))
      exact out (run (Equiv.refl _) rfl rfl rfl h34 (not_not.mp h35) (not_not.mp h45))
    · by_cases h35 : Mixing μ W S X T 3 5
      · have h45 : ¬ Mixing μ W S X T 4 5 := fun h => hmany (Or.inr (Or.inr ⟨h35,h⟩))
        let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,1,2,3,5,4] (by decide)
        exact out (run σ rfl rfl rfl h35 (not_not.mp h34) (reverse 4 5 (by decide) (not_not.mp h45)))
      · by_cases h45 : Mixing μ W S X T 4 5
        · let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![0,1,2,4,5,3] (by decide)
          exact out (run σ rfl rfl rfl h45 (reverse 3 4 (by decide) (not_not.mp h34))
            (reverse 3 5 (by decide) (not_not.mp h35)))
        · exact ⟨X,hX,mX,ThirdsCaseBNoMixing.three_nonmixing_twin μ W hW bW sW hpart
            S X hS hX hXS d hd mS mX hr T hf h0 hc hcl1 hcl2 haY
            (not_not.mp h34) (not_not.mp h35) (not_not.mp h45)⟩
end ThirdsCaseBComplete
end JigBundleModule151

/- Inlined module Statements.E811ThirdsTwin; original SHA256 041e6ad48a426f2d11fca3ffea3defac187343ef6e03a7f3d677ae60161a184b -/
section JigBundleModule152

open MeasureTheory
open scoped BigOperators

namespace Submissions.E811ThirdsTwin.Canonical

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₄) *
    W (σ 4) (x₄, x₅) * W (σ 5) (x₅, x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

noncomputable def setIndicator {Ω : Type*} (S : Set Ω) (x : Ω) : ℝ := by
  classical
  exact if x ∈ S then 1 else 0

/-- A one-third set with deterministic color transport forces a full twin set
of mass one sixth in a balanced rainbow-C6-free kernel system. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 6 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x, y) ∂μ) = (1 / 6 : ℝ)) →
      (∀ σ : Equiv.Perm (Fin 6), cycleDensity μ W σ = 0) →
      ∀ V : Set Ω, MeasurableSet V → μ.real V = (1 / 3 : ℝ) →
      (∀ c, ∀ᵐ x ∂μ,
        (∫ y in V, W c (x, y) ∂μ) = 0 ∨
        (∫ y in V, W c (x, y) ∂μ) = (1 / 6 : ℝ)) →
      ∃ X : Set Ω, MeasurableSet X ∧ μ.real X = (1 / 6 : ℝ) ∧
        ∀ c : Fin 6, ∃ T : Set Ω, MeasurableSet T ∧
          μ.real T = (1 / 6 : ℝ) ∧
          (∀ᵐ p ∂μ.prod μ, p.1 ∈ X → W c p = setIndicator T p.2)

end Submissions.E811ThirdsTwin.Canonical
end JigBundleModule152

/- Inlined module ThirdsTwinFinal; original SHA256 94d7fd953cdbdc81ff4bfecddb4fa5e6234243f07f923d2b60a256a58da779b6 -/
section JigBundleModule153
open MeasureTheory
namespace ThirdsTwinFinal
open TwoPairHalfSetOperator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma thirds_twin (W : Fin 6 → Ω × Ω → ℝ)
    (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (hpart : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (d : ℝ) (hd : 0<d) (hr : ∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x,y) ∂μ=d)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ.real S=2*d)
    (hend : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨ (∫ y in S, W c (x,y) ∂μ)=d)
    (hz : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0) :
    ∃ I : Set Ω, MeasurableSet I ∧ μ.real I=d ∧
      ∀ c, ∃ T : Set Ω, MeasurableSet T ∧ μ.real T=d ∧
        (∀ᵐ p ∂μ.prod μ, p.1∈I → W c p=oneSet T p.2) := by
  have part (σ : Equiv.Perm (Fin 6)) : ∀ᵐ p ∂μ.prod μ, ∑ c, W (σ c) p=1 := by
    filter_upwards [hpart] with p hp
    rw [Equiv.sum_comp σ (fun c => W c p)]; exact hp
  have cycles (σ : Equiv.Perm (Fin 6)) : ∀ τ : Equiv.Perm (Fin 6),
      LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ (τ c)))=0 := by
    intro τ; exact hz (τ.trans σ)
  rcases ThirdsNormalizedStarting.normalize μ W hW bW sW hpart d hd hr S hS mS hend with ha | hb
  · obtain ⟨a⟩ := ha
    obtain ⟨I,hI,mI,targets⟩ := ThirdsCaseATwin.case_a_twin μ (fun c => W (a.σ c))
      (fun c => hW (a.σ c)) (fun c => bW (a.σ c)) (fun c => sW (a.σ c)) (part a.σ)
      d hd (fun c => hr (a.σ c)) S hS mS (fun c => hend (a.σ c)) a.hi0 a.hi1 a.hCD (cycles a.σ)
    refine ⟨I,hI,mI,?_⟩
    intro c
    simpa only [a.σ.apply_symm_apply] using targets (a.σ.symm c)
  · obtain ⟨b⟩ := hb
    obtain ⟨I,hI,mI,targets⟩ := ThirdsCaseBComplete.case_b_twin μ (fun c => W (b.σ c))
      (fun c => hW (b.σ c)) (fun c => bW (b.σ c)) (fun c => sW (b.σ c)) (part b.σ)
      S b.X hS b.hX b.hXS d hd mS b.mX (fun c => hr (b.σ c)) b.T b.hT b.hf b.h0 b.hc
      b.hcl1 b.hcl2 b.haX b.haY (cycles b.σ) b.hm b.mb b.mc b.mD b.mE b.mF
    refine ⟨I,hI,mI,?_⟩
    intro c
    simpa only [b.σ.apply_symm_apply] using targets (b.σ.symm c)
end ThirdsTwinFinal

namespace Submissions.E811ThirdsTwin.Complete
 theorem proof : Submissions.E811ThirdsTwin.Canonical.statement := by
  intro Ω inst μ hμ
  let : IsProbabilityMeasure μ := hμ
  intro W hW bW sW hpart hr hz S hS mS hend
  have cycles : ∀ σ : Equiv.Perm (Fin 6),
      LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0 := by
    intro σ
    exact hz σ
  have mS' : μ.real S=2*(1/6:ℝ) := by rw [mS]; norm_num
  obtain ⟨I,hI,mI,targets⟩ := ThirdsTwinFinal.thirds_twin μ W hW bW sW hpart
    (1/6) (by norm_num) hr S hS mS' hend cycles
  refine ⟨I,hI,mI,?_⟩
  intro c
  obtain ⟨T,hT,mT,ht⟩ := targets c
  refine ⟨T,hT,mT,?_⟩
  simpa [TwoPairHalfSetOperator.oneSet,Submissions.E811ThirdsTwin.Canonical.setIndicator,Set.indicator] using ht
end Submissions.E811ThirdsTwin.Complete
end JigBundleModule153

/- Inlined module D10NoThirdsTransport; original SHA256 da7ae020e9d1a49353d5c95ab0e571e41ab98a987721b3bac0b4c917f3cec45f -/
section JigBundleModule154
open MeasureTheory
namespace D10NoThirdsTransport
open TwoPairHalfSetOperator D10BlockPropagationCore
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
lemma impossible (W : Fin 6 → Ω×Ω → ℝ) (hW : ∀ c, Measurable (W c))
    (bW : ∀ c, ∀ᵐ p ∂μ.prod μ, 0≤W c p ∧ W c p≤1)
    (sW : ∀ c, ∀ᵐ p ∂μ.prod μ, W c p=W c (p.2,p.1))
    (part : ∀ᵐ p ∂μ.prod μ, ∑ c, W c p=1)
    (degree : ∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x,y) ∂μ)=(1:ℝ)/6)
    (cycles : ∀ σ : Equiv.Perm (Fin 6), LowSupportCycle.cycleNested (μ := μ) (fun c => W (σ c))=0)
    (triangles : ∀ i j c : Fin 6, i≠j → c≠i → c≠j → ¬palette i j c →
      (∫ z, ∫ x, ∫ y, W i (z,x)*W c (x,y)*W j (y,z) ∂μ ∂μ ∂μ)=0)
    (S : Set Ω) (hS : MeasurableSet S) (mS : μ.real S=(1:ℝ)/3)
    (transport : ∀ c, ∀ᵐ x ∂μ, (∫ y in S, W c (x,y) ∂μ)=0 ∨
      (∫ y in S, W c (x,y) ∂μ)=(1:ℝ)/6) : False := by
  have ms : μ.real S=2*((1:ℝ)/6) := by rw [mS]; norm_num
  obtain ⟨I,hI,mI,ht⟩ := ThirdsTwinFinal.thirds_twin μ W hW bW sW part
    ((1:ℝ)/6) (by norm_num) degree S hS ms transport cycles
  choose T hT mT hf using ht
  have twins (c : Fin 6) : ∀ᵐ x ∂μ.restrict I,
      (fun y => W c (x,y)) =ᵐ[μ] oneSet (T c) := by
    apply (ae_restrict_iff' hI).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod (hf c)] with x hx
    intro hi
    exact hx.mono (fun _ h => h hi)
  exact D10JointTwinExclusion.impossible μ W hW bW sW part degree cycles triangles I hI mI T hT twins
end D10NoThirdsTransport
end JigBundleModule154

/- Inlined module Statements.E811D10NoThirds; original SHA256 c40b84b40d77c4cf3aaf01cb2582af3311e29b06c725f2189bce7d5a6f1a8a6d -/
section JigBundleModule155
open MeasureTheory
open scoped BigOperators
namespace Submissions.E811D10NoThirds.Canonical

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₄) *
    W (σ 4) (x₄, x₅) * W (σ 5) (x₅, x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

/-- The displayed ten rainbow-triangle palettes, in the fixed color labeling. -/
def allowedPalette (i j c : Fin 6) : Prop :=
  ({i,j,c} : Finset (Fin 6)) ∈
    ({{0,1,5},{0,2,4},{0,3,4},{0,3,5},{1,2,3},{1,3,4},{1,4,5},{2,3,5},{2,4,5},{3,4,5}} : Finset (Finset (Fin 6)))

noncomputable def triangleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (i j c : Fin 6) : ℝ :=
  ∫ z, ∫ x, ∫ y, W i (z,x) * W c (x,y) * W j (y,z) ∂μ ∂μ ∂μ

/-- A balanced symmetric D10 kernel with zero rainbow six-cycle density has
no measurable one-third set with deterministic endpoint color transport. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 6 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x, y) ∂μ) = (1 / 6 : ℝ)) →
      (∀ σ : Equiv.Perm (Fin 6), cycleDensity μ W σ = 0) →
      (∀ i j c : Fin 6, i ≠ j → c ≠ i → c ≠ j → ¬allowedPalette i j c →
        triangleDensity μ W i j c = 0) →
      ∀ S : Set Ω, MeasurableSet S → μ.real S = (1 / 3 : ℝ) →
      (∀ c, ∀ᵐ x ∂μ,
        (∫ y in S, W c (x, y) ∂μ) = 0 ∨
        (∫ y in S, W c (x, y) ∂μ) = (1 / 6 : ℝ)) → False

end Submissions.E811D10NoThirds.Canonical
end JigBundleModule155

/- Inlined module D10NoThirdsFinal; original SHA256 364e37d9310e4fe8a779de84703c80262f4eca9e4bf3b914e15fd5e506621755 -/
section JigBundleModule156
namespace Submissions.E811D10NoThirds.Complete
open MeasureTheory
 theorem proof : Submissions.E811D10NoThirds.Canonical.statement := by
  intro Ω inst μ hμ
  let : IsProbabilityMeasure μ := hμ
  intro W hW bW sW part degree cycles triangles S hS mS transport
  exact D10NoThirdsTransport.impossible μ W hW bW sW part degree cycles triangles S hS mS transport
end Submissions.E811D10NoThirds.Complete
end JigBundleModule156

#print axioms Submissions.E811D10NoThirds.Complete.proof
