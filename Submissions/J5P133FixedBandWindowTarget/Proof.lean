import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Ascoli

namespace Submissions.J5P133FixedBandWindowTarget

section File_FixedTargetDensity

/-!
# Fixed-target normalized neighborhood leakage

Lebesgue density for one fixed measurable target, at the original n denominator.
No quantitative differentiation rate or regularity of the target is assumed.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Jig133.FixedTargetDensity

def leak (E : Set ℝ) (r x : ℝ) : ℝ := volume.real (closedBall x r \ E)

def scaledLeak (E : Set ℝ) (k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * leak E (k / n) x

theorem leak_nonneg (E : Set ℝ) (r x : ℝ) : 0 ≤ leak E r x :=
  measureReal_nonneg

theorem measurable_leak {E : Set ℝ} (hE : MeasurableSet E) (r : ℝ) :
    Measurable (leak E r) := by
  let S : Set (ℝ × ℝ) := {p | dist p.2 p.1 ≤ r ∧ p.2 ∉ E}
  have hS : MeasurableSet S :=
    (measurableSet_le (measurable_snd.dist measurable_fst) measurable_const).inter
      (hE.compl.preimage measurable_snd)
  exact (measurable_measure_prodMk_left (ν := volume) hS).ennreal_toReal

theorem measurable_scaledLeak {E : Set ℝ} (hE : MeasurableSet E) (k : ℝ) (n : ℕ) :
    Measurable (scaledLeak E k n) :=
  (measurable_leak hE (k / n)).const_mul (n : ℝ)

theorem scaledLeak_nonneg (E : Set ℝ) (k : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ scaledLeak E k n x := mul_nonneg (Nat.cast_nonneg _) (leak_nonneg _ _ _)

theorem scaledLeak_eq {E : Set ℝ} (hE : MeasurableSet E)
    {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    scaledLeak E k n x = 2 * k *
      (1 - (volume (E ∩ closedBall x (k / n)) /
        volume (closedBall x (k / n))).toReal) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 ≤ 2 * (k / n) := by positivity
  have hsum := measureReal_sdiff_add_inter (μ := volume)
    (s := closedBall x (k / n)) hE
    (by rw [Real.volume_closedBall]; finiteness)
  have hvol : volume.real (closedBall x (k / n)) = 2 * (k / n) := by
    simp only [measureReal_def, Real.volume_closedBall, ENNReal.toReal_ofReal hr]
  rw [hvol, inter_comm] at hsum
  simp only [scaledLeak, leak, ENNReal.toReal_div, Real.volume_closedBall,
    ENNReal.toReal_ofReal hr]
  change (n : ℝ) * volume.real (closedBall x (k / n) \ E) =
    2 * k * (1 - volume.real (E ∩ closedBall x (k / n)) / (2 * (k / n)))
  rw [show volume.real (closedBall x (k / n) \ E) =
    2 * (k / n) - volume.real (E ∩ closedBall x (k / n)) by linarith]
  field_simp [hk.ne', hnR.ne']

theorem ae_tendsto_scaledLeak {E : Set ℝ} (hE : MeasurableSet E)
    {k : ℝ} (hk : 0 < k) :
    ∀ᵐ x ∂volume.restrict E,
      Tendsto (fun n : ℕ => scaledLeak E k n x) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => k / (n : ℝ)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat k, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_pos hk (Nat.cast_pos.mpr (by omega))
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div
    (volume : Measure ℝ) E] with x hx
  have hd := hx.comp hr
  have hdR := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hd
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub hdR).const_mul (2 * k)
  have ht0 : Tendsto (fun n : ℕ => 2 * k *
      (1 - (volume (E ∩ closedBall x (k / n)) /
        volume (closedBall x (k / n))).toReal)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_one, sub_self, mul_zero, Function.comp_def] using ht
  apply ht0.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (scaledLeak_eq hE hk (by omega) x).symm

theorem tendsto_bad_mass {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤)
    {k ε : ℝ} (hk : 0 < k) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => volume.real (E ∩ {x | ε ≤ scaledLeak E k n x}))
      atTop (𝓝 0) := by
  let : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hfin.lt_top⟩
  have ht : TendstoInMeasure (volume.restrict E) (scaledLeak E k) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => (measurable_scaledLeak hE k n).aestronglyMeasurable)
      (ae_tendsto_scaledLeak hE hk)
  have hb := (tendstoInMeasure_iff_measureReal_norm.mp ht) ε hε
  simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (scaledLeak_nonneg E k _ _),
    measureReal_def, Measure.restrict_apply₀
      (measurableSet_le measurable_const (measurable_scaledLeak hE k _)).nullMeasurableSet,
    inter_comm] using hb

end Jig133.FixedTargetDensity

end
end File_FixedTargetDensity

section File_SlowDensityDiagonal

/-!
# A slow diagonal with a sublinear radius

Each fixed accuracy level holds eventually. Select increasing accuracy levels
while retaining that property and the square bound needed for shrinking radii.
-/

noncomputable section
open Filter
open scoped Topology
namespace Jig133.SlowDensityDiagonal

theorem exists_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ q : ℕ → ℕ, Monotone q ∧ Tendsto q atTop atTop ∧
      ∀ᶠ n in atTop, P (q n) n ∧ (q n + 1) ^ 2 ≤ n := by
  classical
  have hN : ∀ k, ∃ N : ℕ, k ≤ N ∧
      ∀ n, N ≤ n → P k n ∧ (k + 1) ^ 2 ≤ n := by
    intro k
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hP k)
    refine ⟨max N (max k ((k + 1) ^ 2)), ?_, ?_⟩
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · intro n hn
      exact ⟨hN n ((le_max_left _ _).trans hn),
        ((le_max_right _ _).trans (le_max_right _ _)).trans hn⟩
  choose N hNk hNP using hN
  let q : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hmono : Monotone q := by
    intro n m hnm
    exact Nat.findGreatest_mono (fun _ hk => hk.trans hnm) hnm
  have htop : Tendsto q atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (N k)] with n hn
    exact Nat.le_findGreatest ((hNk k).trans hn) hn
  refine ⟨q, hmono, htop, ?_⟩
  filter_upwards [eventually_ge_atTop (N 0)] with n hn
  exact hNP (q n) n (Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn)

theorem ratio_tendsto_zero {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hsq : ∀ᶠ n in atTop, (q n + 1) ^ 2 ≤ n) :
    Tendsto (fun n : ℕ => ((q n + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have hden : Tendsto (fun n => ((q n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n => Nat.le_succ (q n)) hq)
  have hinv : Tendsto (fun n => 1 / ((q n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hinv
  filter_upwards [hsq] with n hn
  have hqpos : (0 : ℝ) < ((q n + 1 : ℕ) : ℝ) := by positivity
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by nlinarith [Nat.zero_le (q n)])
  apply (div_le_div_iff₀ hnpos hqpos).mpr
  have hs : (((q n + 1 : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

end Jig133.SlowDensityDiagonal

end
end File_SlowDensityDiagonal

section File_FixedTargetHalos

/-!
# One slow halo sequence for a fixed measurable target

The sequence is chosen before every later fixed geometric scale. A family of
at most n good anchor halos has total complement leakage tending to zero.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Jig133.FixedTargetHalos
open FixedTargetDensity

def good (E : Set ℝ) (R : ℕ → ℕ) (n : ℕ) : Set ℝ :=
  E ∩ {x | scaledLeak E (R n) n x < 1 / (R n : ℝ)}

theorem measurableSet_good {E : Set ℝ} (hE : MeasurableSet E) (R : ℕ → ℕ) (n : ℕ) :
    MeasurableSet (good E R n) :=
  hE.inter (measurableSet_lt (measurable_scaledLeak hE _ _) measurable_const)

theorem bad_eq (E : Set ℝ) (R : ℕ → ℕ) (n : ℕ) :
    E \ good E R n = E ∩ {x | 1 / (R n : ℝ) ≤ scaledLeak E (R n) n x} := by
  ext x
  simp only [good, Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hxE, hx⟩
    exact ⟨hxE, le_of_not_gt (fun hh => hx ⟨hxE, hh⟩)⟩
  · rintro ⟨hxE, hx⟩
    exact ⟨hxE, fun hh => (not_lt_of_ge hx) hh.2⟩

theorem exists_halos {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) :
    ∃ R : ℕ → ℕ, (∀ n, 0 < R n) ∧ Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun n : ℕ => (R n : ℝ) / n) atTop (𝓝 0) ∧
      Tendsto (fun n => volume.real (E \ good E R n)) atTop (𝓝 0) := by
  let P : ℕ → ℕ → Prop := fun k n =>
    volume.real (E ∩ {x | 1 / ((k + 1 : ℕ) : ℝ) ≤
      scaledLeak E (k + 1 : ℕ) n x}) < 1 / ((k + 1 : ℕ) : ℝ)
  have hP : ∀ k, ∀ᶠ n in atTop, P k n := by
    intro k
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have ht := tendsto_bad_mass hE hfin hk (one_div_pos.mpr hk)
    exact (tendsto_order.mp ht).2 _ (one_div_pos.mpr hk)
  obtain ⟨q, hmono, htop, hq⟩ := SlowDensityDiagonal.exists_diagonal P hP
  let R : ℕ → ℕ := fun n => q n + 1
  have hRtop : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (q n)) htop
  refine ⟨R, fun n => Nat.zero_lt_succ _,
    fun n m hnm => Nat.add_le_add_right (hmono hnm) 1, hRtop,
    SlowDensityDiagonal.ratio_tendsto_zero htop (hq.mono fun _ h => h.2), ?_⟩
  have hinv : Tendsto (fun n => 1 / (R n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hRtop)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hinv
  filter_upwards [hq] with n hn
  rw [bad_eq]
  exact hn.1.le

theorem leak_lt_of_good {E : Set ℝ} {R : ℕ → ℕ} {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : x ∈ good E R n) :
    leak E ((R n : ℝ) / n) x < 1 / ((R n : ℝ) * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : leak E ((R n : ℝ) / n) x < (1 / (R n : ℝ)) / n := by
    apply (lt_div_iff₀ hnR).mpr
    simpa only [scaledLeak, mem_ofPred_eq, mul_comm] using hx.2
  simpa only [div_div] using hh

def halos (R : ℕ → ℕ) (n : ℕ) (S : Finset ℝ) : Set ℝ :=
  ⋃ x ∈ S, closedBall x ((R n : ℝ) / n)

theorem union_leak_le {E : Set ℝ} {R : ℕ → ℕ} {n : ℕ}
    (hn : 0 < n) (hR : 0 < R n) (S : Finset ℝ) (hcard : S.card ≤ n)
    (hS : ∀ x ∈ S, x ∈ good E R n) :
    volume.real (halos R n S \ E) ≤ 1 / (R n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRR : (0 : ℝ) < R n := by exact_mod_cast hR
  simp only [halos, iUnion_sdiff]
  calc
    _ ≤ ∑ x ∈ S, leak E ((R n : ℝ) / n) x := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ S, 1 / ((R n : ℝ) * n) :=
      Finset.sum_le_sum fun x hx => (leak_lt_of_good hn (hS x hx)).le
    _ = (S.card : ℝ) * (1 / ((R n : ℝ) * n)) := by simp
    _ ≤ (n : ℝ) * (1 / ((R n : ℝ) * n)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
    _ = 1 / (R n : ℝ) := by field_simp [hnR.ne', hRR.ne']

/-- Every fixed source-neighborhood scale eventually fits the already chosen halos. -/
theorem eventually_covers_fixed_scale {R : ℕ → ℕ} (hR : Tendsto R atTop atTop)
    (C s : ℝ) : ∀ᶠ n : ℕ in atTop, ∀ x y : ℝ, dist y x ≤ C / n →
      closedBall y (s / n) ⊆ closedBall x ((R n : ℝ) / n) := by
  have hRR : Tendsto (fun n => (R n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hR
  filter_upwards [hRR.eventually_ge_atTop (C + s), eventually_ge_atTop 1] with n hn hn1
  intro x y hy
  apply closedBall_subset_closedBall'
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    s / n + dist y x ≤ s / n + C / n := add_le_add le_rfl hy
    _ = (C + s) / n := by ring
    _ ≤ (R n : ℝ) / n := div_le_div_of_nonneg_right hn hnR.le

end Jig133.FixedTargetHalos

end
end File_FixedTargetHalos

section File_LocalHaloBudget

/-!
# Local exceptional-mass budgets inside the fixed-target halos

Arbitrary subsets and arbitrarily overlapping source microbands are allowed.
The cost is charged to at most n anchor halos, not to the number of microbands.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Jig133.LocalHaloBudget
open FixedTargetHalos

theorem halos_finite (R : ℕ → ℕ) (n : ℕ) (S : Finset ℝ) :
    volume (halos R n S) ≠ ⊤ := by
  apply measure_biUnion_ne_top S.finite_toSet
  intro x _
  rw [Real.volume_closedBall]
  exact ENNReal.ofReal_ne_top

theorem subset_leak_le {E V : Set ℝ} {R : ℕ → ℕ} {n : ℕ}
    (hn : 0 < n) (hR : 0 < R n) (S : Finset ℝ) (hcard : S.card ≤ n)
    (hS : ∀ x ∈ S, x ∈ good E R n) (hV : V ⊆ halos R n S) :
    volume.real (V \ E) ≤ 1 / (R n : ℝ) := by
  apply (measureReal_mono (sdiff_subset_sdiff_left hV)
    (measure_ne_top_of_subset sdiff_subset (halos_finite R n S))).trans
  exact union_leak_le hn hR S hcard hS

theorem local_bad_mass_le {E V B : Set ℝ} (hEfin : volume E ≠ ⊤)
    {R : ℕ → ℕ} {n : ℕ} (hn : 0 < n) (hR : 0 < R n)
    (S : Finset ℝ) (hcard : S.card ≤ n) (hS : ∀ x ∈ S, x ∈ good E R n)
    (hV : V ⊆ halos R n S) :
    volume.real (V ∩ B) ≤ volume.real (E ∩ B) + 1 / (R n : ℝ) := by
  have hs : V ∩ B ⊆ (E ∩ B) ∪ (V \ E) := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inl ⟨he, hx.2⟩
    · exact Or.inr ⟨hx.1, he⟩
  have hefin : volume (E ∩ B) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hEfin
  have hvfin : volume (V \ E) ≠ ⊤ :=
    measure_ne_top_of_subset (sdiff_subset.trans hV) (halos_finite R n S)
  calc
    _ ≤ volume.real ((E ∩ B) ∪ (V \ E)) :=
      measureReal_mono hs (measure_union_lt_top hefin.lt_top hvfin.lt_top).ne
    _ ≤ volume.real (E ∩ B) + volume.real (V \ E) := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (subset_leak_le hn hR S hcard hS hV)

/-- The halo sequence precedes C and s; the later cutoff can depend on them. -/
theorem eventually_microband_leak {E : Set ℝ} {R : ℕ → ℕ}
    (hpos : ∀ n, 0 < R n) (htop : Tendsto R atTop atTop) (C s : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ S T : Finset ℝ, S.card ≤ n →
      (∀ x ∈ S, x ∈ good E R n) →
      (∀ y ∈ T, ∃ x ∈ S, dist y x ≤ C / n) →
      volume.real ((⋃ y ∈ T, closedBall y (s / n)) \ E) ≤ 1 / (R n : ℝ) := by
  filter_upwards [eventually_covers_fixed_scale htop C s, eventually_ge_atTop 1]
    with n hcover hn
  intro S T hcard hS hT
  apply subset_leak_le (by omega) (hpos n) S hcard hS
  rintro z hz
  obtain ⟨y, hy, hz⟩ := mem_iUnion₂.mp hz
  obtain ⟨x, hx, hdist⟩ := hT y hy
  exact mem_iUnion₂.mpr ⟨x, hx, hcover x y hdist hz⟩

end Jig133.LocalHaloBudget

end
end File_LocalHaloBudget

section File_DensityInverseSquare

open scoped BigOperators

namespace Jig133.DensityInverseSquare

noncomputable section

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- A finite truncation. The index is retained, so equal distance values are
counted with their original multiplicity. -/
def truncated (d : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i, if d i < r then 1 / (d i) ^ 2 else 0

/-- The count in one closed ball bounds one dyadic step. This bound does not
assume the desired inverse-square sum and does not discard any index. -/
theorem truncated_step (d : ι → ℝ) (A r : ℝ) (hr : 0 < r)
    (hcount : ((Finset.univ.filter (fun i => d i ≤ 2 * r)).card : ℝ) ≤
      A * (2 * r)) :
    truncated d (2 * r) ≤ truncated d r + 2 * A / r := by
  classical
  have hsquare : 0 < r ^ 2 := sq_pos_of_pos hr
  have hpoint (i : ι) :
      (if d i < 2 * r then 1 / (d i) ^ 2 else 0) ≤
        (if d i < r then 1 / (d i) ^ 2 else 0) +
          (if d i < 2 * r then 1 / r ^ 2 else 0) := by
    by_cases hi2 : d i < 2 * r
    · by_cases hi : d i < r
      · simp only [hi2, hi, ite_true]
        exact le_add_of_nonneg_right (one_div_nonneg.mpr hsquare.le)
      · simp only [hi2, hi, ite_true, ite_false, zero_add]
        have hri : r ≤ d i := le_of_not_gt hi
        exact one_div_le_one_div_of_le hsquare
          ((sq_le_sq₀ hr.le (hr.le.trans hri)).mpr hri)
    · simp only [hi2, ite_false]
      split_ifs <;> positivity
  have hcard : ((Finset.univ.filter (fun i => d i < 2 * r)).card : ℝ) ≤
      ((Finset.univ.filter (fun i => d i ≤ 2 * r)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (show
      Finset.univ.filter (fun i => d i < 2 * r) ⊆
        Finset.univ.filter (fun i => d i ≤ 2 * r) from by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.le⟩)
  have hconstant : (∑ i, if d i < 2 * r then 1 / r ^ 2 else 0) ≤
      2 * A / r := by
    calc
      _ = ((Finset.univ.filter (fun i => d i < 2 * r)).card : ℝ) *
          (1 / r ^ 2) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A * (2 * r)) * (1 / r ^ 2) :=
        mul_le_mul_of_nonneg_right (hcard.trans hcount)
          (one_div_nonneg.mpr hsquare.le)
      _ = 2 * A / r := by
        field_simp [ne_of_gt hr]
  calc
    truncated d (2 * r) ≤ truncated d r +
        (∑ i, if d i < 2 * r then 1 / r ^ 2 else 0) := by
      unfold truncated
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ truncated d r + 2 * A / r := add_le_add le_rfl hconstant

/-- The finite geometric estimate is kept with its actual nonnegative remainder.
No infinite sum or convergence result is needed. -/
theorem truncated_dyadic_le (d : ι → ℝ) (a A : ℝ) (ha : 0 < a)
    (hmin : ∀ i, a ≤ d i)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i => d i ≤ r)).card : ℝ) ≤ A * r)
    (N : ℕ) :
    truncated d (a * 2 ^ N) ≤ 4 * A / a - 4 * A / (a * 2 ^ N) := by
  induction N with
  | zero =>
      have hz : truncated d a = 0 := by
        unfold truncated
        apply Finset.sum_eq_zero
        intro i _
        exact if_neg (not_lt_of_ge (hmin i))
      simpa only [pow_zero, mul_one, hz, sub_self] using (le_refl (0 : ℝ))
  | succ N ih =>
      have hr : 0 < a * (2 : ℝ) ^ N := mul_pos ha (pow_pos (by norm_num) N)
      have hradius : a * (2 : ℝ) ^ (N + 1) = 2 * (a * 2 ^ N) := by
        rw [pow_succ]
        ring
      rw [hradius]
      calc
        truncated d (2 * (a * 2 ^ N)) ≤ truncated d (a * 2 ^ N) +
            2 * A / (a * 2 ^ N) :=
          truncated_step d A (a * 2 ^ N) hr
            (hcount (2 * (a * 2 ^ N)) (mul_pos (by norm_num) hr))
        _ ≤ (4 * A / a - 4 * A / (a * 2 ^ N)) +
            2 * A / (a * 2 ^ N) := add_le_add ih le_rfl
        _ = 4 * A / a - 4 * A / (2 * (a * 2 ^ N)) := by
          have hscale : 4 * A / (2 * (a * 2 ^ N)) =
              2 * A / (a * 2 ^ N) := by
            field_simp [ne_of_gt ha, pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0)]
            ring
          rw [hscale]
          ring

/-- An all-radius linear count bound and a positive exclusion radius give an
inverse-square bound on the full indexed family, including repeated values. -/
theorem sum_inv_sq_le (d : ι → ℝ) (a A : ℝ) (ha : 0 < a)
    (hmin : ∀ i, a ≤ d i)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i => d i ≤ r)).card : ℝ) ≤ A * r) :
    (∑ i, 1 / (d i) ^ 2) ≤ 4 * A / a := by
  classical
  have hA : 0 ≤ A := by
    have hc := hcount 1 zero_lt_one
    have hn : 0 ≤ ((Finset.univ.filter (fun i => d i ≤ 1)).card : ℝ) :=
      Nat.cast_nonneg _
    nlinarith
  rcases (Finset.univ : Finset ι).eq_empty_or_nonempty with hempty | hnonempty
  · rw [hempty, Finset.sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) hA) ha.le
  · obtain ⟨i₀, _, hmax⟩ := (Finset.univ : Finset ι).exists_max_image d hnonempty
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (d i₀ / a) (by norm_num : (1 : ℝ) < 2)
    have hupper : d i₀ < a * (2 : ℝ) ^ N := by
      have := (div_lt_iff₀ ha).mp hN
      nlinarith
    have hcover (i : ι) : d i < a * (2 : ℝ) ^ N :=
      (hmax i (Finset.mem_univ i)).trans_lt hupper
    have htruncated : truncated d (a * (2 : ℝ) ^ N) = ∑ i, 1 / (d i) ^ 2 := by
      unfold truncated
      exact Finset.sum_congr rfl (fun i _ => if_pos (hcover i))
    have hbound := truncated_dyadic_le d a A ha hmin hcount N
    rw [htruncated] at hbound
    exact hbound.trans (sub_le_self _
      (div_nonneg (mul_nonneg (by norm_num) hA)
        (mul_nonneg ha.le (pow_nonneg (by norm_num) N))))

/-- The full-root form at exclusion radius 4h. The root index is arbitrary:
no injectivity is assumed, and equal roots retain their multiplicity. -/
theorem roots_sum_inv_sq_le (t : ι → ℝ) (c h B : ℝ) (n : ℕ) (hh : 0 < h)
    (hgap : ∀ i, 4 * h ≤ |c - t i|)
    (hdensity : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i => |c - t i| ≤ r)).card : ℝ) ≤
        2 * B * (n : ℝ) * r) :
    (∑ i, 1 / (c - t i) ^ 2) ≤ 2 * B * (n : ℝ) / h := by
  have hbound := sum_inv_sq_le (fun i => |c - t i|) (4 * h)
    (2 * B * (n : ℝ)) (mul_pos (by norm_num) hh) hgap hdensity
  calc
    (∑ i, 1 / (c - t i) ^ 2) = ∑ i, 1 / |c - t i| ^ 2 := by
      simp only [sq_abs]
    _ ≤ 4 * (2 * B * (n : ℝ)) / (4 * h) := hbound
    _ = 2 * B * (n : ℝ) / h := by
      field_simp [ne_of_gt hh]


end
end Jig133.DensityInverseSquare
end File_DensityInverseSquare

section File_ComplexRootStability

/-!
# Stability for every complex root, with multiplicity

Projected roots supply only clearance and counting. The reciprocal sum uses
the actual complex roots and therefore the actual logarithmic derivative.
-/

noncomputable section
open scoped BigOperators
namespace Jig133.ComplexRootStability

theorem projected_distance_le (z : ℂ) (x : ℝ) : |x - z.re| ≤ ‖(x : ℂ) - z‖ := by
  simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm ((x : ℂ) - z)

theorem denominator_comparison (z : ℂ) (q x δ : ℝ) (hclear : δ ≤ |q - z.re|)
    (hx : |x - q| ≤ δ / 2) :
    δ / 2 ≤ ‖(x : ℂ) - z‖ ∧ ‖(q : ℂ) - z‖ ≤ 2 * ‖(x : ℂ) - z‖ := by
  have hq := hclear.trans (projected_distance_le z q)
  have ht : ‖(q : ℂ) - z‖ ≤ |x - q| + ‖(x : ℂ) - z‖ := by
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm q x]
      using dist_triangle (q : ℂ) (x : ℂ) z
  constructor <;> linarith

theorem projected_clearance (z : ℂ) (q x δ a : ℝ) (hclear : δ ≤ |q - z.re|)
    (hx : |x - q| ≤ a) : δ - a ≤ |x - z.re| := by
  have ht := abs_sub_le q x z.re
  rw [abs_sub_comm q x] at ht
  linarith

theorem reciprocal_change_le (z : ℂ) (q x δ : ℝ) (hδ : 0 < δ)
    (hclear : δ ≤ |q - z.re|) (hx : |x - q| ≤ δ / 2) :
    ‖((x : ℂ) - z)⁻¹ - ((q : ℂ) - z)⁻¹‖ ≤
      2 * |x - q| * (1 / ‖(q : ℂ) - z‖ ^ 2) := by
  have hc := denominator_comparison z q x δ hclear hx
  have hq : 0 < ‖(q : ℂ) - z‖ := hδ.trans_le (hclear.trans (projected_distance_le z q))
  have hxp : 0 < ‖(x : ℂ) - z‖ := lt_of_lt_of_le (by linarith) hc.1
  have hzq : (q : ℂ) - z ≠ 0 := norm_pos_iff.mp hq
  have hzx : (x : ℂ) - z ≠ 0 := norm_pos_iff.mp hxp
  have he : ((q : ℂ) - z) - ((x : ℂ) - z) = ((q - x : ℝ) : ℂ) := by
    push_cast
    ring
  calc
    _ = |x - q| / (‖(x : ℂ) - z‖ * ‖(q : ℂ) - z‖) := by
      rw [inv_sub_inv hzx hzq, norm_div, norm_mul, he]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm q x]
    _ ≤ (2 * |x - q|) / ‖(q : ℂ) - z‖ ^ 2 := by
      apply (div_le_div_iff₀ (mul_pos hxp hq) (sq_pos_of_pos hq)).mpr
      have hm := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hc.2 hq.le) (abs_nonneg (x - q))
      nlinarith
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

def slope (z : ι → ℂ) (x : ℝ) : ℝ := ∑ i, (((x : ℂ) - z i)⁻¹).re

theorem inverse_square_le (z : ι → ℂ) (q δ A : ℝ) (hδ : 0 < δ)
    (hclear : ∀ i, δ ≤ |q - (z i).re|)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i => |q - (z i).re| ≤ r)).card : ℝ) ≤ A * r) :
    (∑ i, 1 / ‖(q : ℂ) - z i‖ ^ 2) ≤ 4 * A / δ := by
  classical
  calc
    _ ≤ ∑ i, 1 / |q - (z i).re| ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact one_div_le_one_div_of_le (sq_pos_of_pos (hδ.trans_le (hclear i)))
        ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (projected_distance_le (z i) q))
    _ ≤ _ := DensityInverseSquare.sum_inv_sq_le
      (fun i => |q - (z i).re|) δ A hδ hclear hcount

theorem slope_change_le (z : ι → ℂ) (q x δ A : ℝ) (hδ : 0 < δ)
    (hclear : ∀ i, δ ≤ |q - (z i).re|)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i => |q - (z i).re| ≤ r)).card : ℝ) ≤ A * r)
    (hx : |x - q| ≤ δ / 2) :
    |slope z x - slope z q| ≤ (8 * A / δ) * |x - q| := by
  unfold slope
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(((x : ℂ) - z i)⁻¹).re - (((q : ℂ) - z i)⁻¹).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * |x - q| * (1 / ‖(q : ℂ) - z i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (by simpa only [Complex.sub_re] using
        Complex.abs_re_le_norm (((x : ℂ) - z i)⁻¹ - ((q : ℂ) - z i)⁻¹))
      exact reciprocal_change_le (z i) q x δ hδ (hclear i) hx
    _ = 2 * |x - q| * ∑ i, 1 / ‖(q : ℂ) - z i‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * |x - q| * (4 * A / δ) :=
      mul_le_mul_of_nonneg_left (inverse_square_le z q δ A hδ hclear hcount) (by positivity)
    _ = _ := by ring

end Jig133.ComplexRootStability

end
end File_ComplexRootStability

section File_FullNodalVerticalIncrement

/-!
# Vertical logarithmic increments of the complete nodal polynomial

Every indexed node remains in the product. The center avoids all those nodes;
this also proves that the complex evaluation is nonzero at every real height.
No ordering, distinctness, interval support, or positive height is required.
The empty product and repeated node values are included.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace Jig133.FullNodalVerticalIncrement

variable {ι : Type*}

/-- Complex evaluation of the actual real nodal polynomial retains every factor. -/
theorem eval₂_nodal (s : Finset ι) (nodes : ι → ℝ) (z : ℂ) :
    (Lagrange.nodal s nodes).eval₂ Complex.ofRealHom z =
      ∏ i ∈ s, (z - (nodes i : ℂ)) := by
  simp only [Lagrange.nodal, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Complex.ofRealHom_eq_coe]

/-- A vertical factor has nonzero real part whenever the center avoids its node. -/
theorem vertical_factor_ne_zero (c α t : ℝ) (hc : c ≠ t) :
    (c : ℂ) + (α : ℂ) * Complex.I - (t : ℂ) ≠ 0 := by
  intro h
  apply sub_ne_zero.mpr hc
  simpa using congrArg Complex.re h

/-- In particular the complete complex nodal evaluation is genuinely nonzero. -/
theorem eval₂_nodal_ne_zero (s : Finset ι) (nodes : ι → ℝ) (c α : ℝ)
    (hc : ∀ i ∈ s, c ≠ nodes i) :
    (Lagrange.nodal s nodes).eval₂ Complex.ofRealHom
      ((c : ℂ) + (α : ℂ) * Complex.I) ≠ 0 := by
  rw [eval₂_nodal]
  exact Finset.prod_ne_zero_iff.mpr (fun i hi =>
    vertical_factor_ne_zero c α (nodes i) (hc i hi))

/-- The squared complex modulus of one actual vertical factor. -/
theorem norm_sq_vertical_sub (c α t : ℝ) :
    ‖(c : ℂ) + (α : ℂ) * Complex.I - (t : ℂ)‖ ^ 2 =
      (c - t) ^ 2 + α ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

/-- The scalar increment identity, with all logarithmic product factors nonzero. -/
theorem vertical_log_increment_eq (c α t : ℝ) (hc : c ≠ t) :
    Real.log ‖(c : ℂ) + (α : ℂ) * Complex.I - (t : ℂ)‖ -
        Real.log |c - t| =
      (1 / 2 : ℝ) * Real.log (1 + α ^ 2 / (c - t) ^ 2) := by
  have hd : (c - t) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hc)
  have hq : 0 ≤ α ^ 2 / (c - t) ^ 2 :=
    div_nonneg (sq_nonneg α) (sq_nonneg (c - t))
  have hp : 0 < 1 + α ^ 2 / (c - t) ^ 2 :=
    add_pos_of_pos_of_nonneg zero_lt_one hq
  have hfactor : (c - t) ^ 2 + α ^ 2 =
      (c - t) ^ 2 * (1 + α ^ 2 / (c - t) ^ 2) := by
    symm
    rw [mul_add, mul_one, mul_div_cancel₀ _ hd]
  have hlog :
      (2 : ℝ) * Real.log ‖(c : ℂ) + (α : ℂ) * Complex.I - (t : ℂ)‖ =
        2 * Real.log |c - t| + Real.log (1 + α ^ 2 / (c - t) ^ 2) := by
    calc
      (2 : ℝ) * Real.log ‖(c : ℂ) + (α : ℂ) * Complex.I - (t : ℂ)‖ =
          Real.log (‖(c : ℂ) + (α : ℂ) * Complex.I - (t : ℂ)‖ ^ 2) := by
        exact (Real.log_pow
          ‖(c : ℂ) + (α : ℂ) * Complex.I - (t : ℂ)‖ 2).symm
      _ = Real.log ((c - t) ^ 2 + α ^ 2) := by rw [norm_sq_vertical_sub]
      _ = Real.log ((c - t) ^ 2 * (1 + α ^ 2 / (c - t) ^ 2)) := by rw [hfactor]
      _ = Real.log ((c - t) ^ 2) + Real.log (1 + α ^ 2 / (c - t) ^ 2) :=
        Real.log_mul hd hp.ne'
      _ = 2 * Real.log |c - t| + Real.log (1 + α ^ 2 / (c - t) ^ 2) := by
        simp [Real.log_pow, Real.log_abs]
  linarith

/-- Exact vertical increment for the complete real nodal polynomial. -/
theorem full_nodal_increment_eq (s : Finset ι) (nodes : ι → ℝ) (c α : ℝ)
    (hc : ∀ i ∈ s, c ≠ nodes i) :
    Real.log ‖(Lagrange.nodal s nodes).eval₂ Complex.ofRealHom
        ((c : ℂ) + (α : ℂ) * Complex.I)‖ -
        Real.log |(Lagrange.nodal s nodes).eval c| =
      (1 / 2 : ℝ) * ∑ i ∈ s, Real.log (1 + α ^ 2 / (c - nodes i) ^ 2) := by
  have hn : ∀ i ∈ s,
      ‖(c : ℂ) + (α : ℂ) * Complex.I - (nodes i : ℂ)‖ ≠ 0 := by
    intro i hi
    exact norm_ne_zero_iff.mpr (vertical_factor_ne_zero c α (nodes i) (hc i hi))
  have hr : ∀ i ∈ s, c - nodes i ≠ 0 := fun i hi => sub_ne_zero.mpr (hc i hi)
  rw [eval₂_nodal, norm_prod, Real.log_prod hn, Real.log_abs,
    Lagrange.eval_nodal, Real.log_prod hr, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Real.log_abs] using vertical_log_increment_eq c α (nodes i) (hc i hi)

/-- The vertical increment is nonnegative, including at height zero. -/
theorem full_nodal_increment_nonneg (s : Finset ι) (nodes : ι → ℝ) (c α : ℝ)
    (hc : ∀ i ∈ s, c ≠ nodes i) :
    0 ≤ Real.log ‖(Lagrange.nodal s nodes).eval₂ Complex.ofRealHom
        ((c : ℂ) + (α : ℂ) * Complex.I)‖ -
        Real.log |(Lagrange.nodal s nodes).eval c| := by
  rw [full_nodal_increment_eq s nodes c α hc]
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_nonneg
  intro i hi
  apply Real.log_nonneg
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg α) (sq_nonneg (c - nodes i)))

/-- The actual full-product increment is bounded by its full inverse-square sum. -/
theorem full_nodal_increment_le (s : Finset ι) (nodes : ι → ℝ) (c α : ℝ)
    (hc : ∀ i ∈ s, c ≠ nodes i) :
    Real.log ‖(Lagrange.nodal s nodes).eval₂ Complex.ofRealHom
        ((c : ℂ) + (α : ℂ) * Complex.I)‖ -
        Real.log |(Lagrange.nodal s nodes).eval c| ≤
      (α ^ 2 / 2) * ∑ i ∈ s, 1 / (c - nodes i) ^ 2 := by
  rw [full_nodal_increment_eq s nodes c α hc]
  calc
    (1 / 2 : ℝ) * ∑ i ∈ s, Real.log (1 + α ^ 2 / (c - nodes i) ^ 2) ≤
        (1 / 2 : ℝ) * ∑ i ∈ s, α ^ 2 / (c - nodes i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      apply Finset.sum_le_sum
      intro i hi
      have hq : 0 ≤ α ^ 2 / (c - nodes i) ^ 2 :=
        div_nonneg (sq_nonneg α) (sq_nonneg (c - nodes i))
      have hp : 0 < 1 + α ^ 2 / (c - nodes i) ^ 2 :=
        add_pos_of_pos_of_nonneg zero_lt_one hq
      have hlog := Real.log_le_sub_one_of_pos hp
      linarith
    _ = (α ^ 2 / 2) * ∑ i ∈ s, 1 / (c - nodes i) ^ 2 := by
      simp_rw [div_eq_mul_inv, one_mul]
      rw [← Finset.mul_sum]
      ring

end Jig133.FullNodalVerticalIncrement

end
end File_FullNodalVerticalIncrement

section File_FullNodalBandGain

open Set Polynomial
open scoped BigOperators

namespace Jig133.FullNodalBandGain

noncomputable section

/-- On its nonzero locus the absolute logarithm has the actual logarithmic derivative. -/
theorem hasDerivAt_log_abs_eval (P : ℝ[X]) {x : ℝ} (hx : P.eval x ≠ 0) :
    HasDerivAt (fun y => Real.log |P.eval y|) (P.derivative.eval x / P.eval x) x := by
  simpa only [Real.log_abs] using (P.hasDerivAt x).log hx

/-- A positive lower logarithmic slope gives a genuine real logarithmic gain. -/
theorem real_gain_of_lower_slope (P : ℝ[X]) {c x L : ℝ} (hcx : c ≤ x)
    (hroot : ∀ y ∈ Icc c x, P.eval y ≠ 0)
    (hslope : ∀ y ∈ Icc c x, L ≤ P.derivative.eval y / P.eval y) :
    L * (x - c) ≤ Real.log |P.eval x| - Real.log |P.eval c| := by
  have hd : ∀ y ∈ Icc c x,
      HasDerivAt (fun z => Real.log |P.eval z|) (P.derivative.eval y / P.eval y) y :=
    fun y hy => hasDerivAt_log_abs_eval P (hroot y hy)
  apply (convex_Icc c x).mul_sub_le_image_sub_of_le_deriv
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    (fun y hy => by rw [(hd y (interior_subset hy)).deriv]; exact hslope y (interior_subset hy))
    c ⟨le_rfl, hcx⟩ x ⟨hcx, le_rfl⟩ hcx

/-- A negative upper slope gives the same gain in the leftward direction. -/
theorem real_gain_of_upper_slope (P : ℝ[X]) {c x L : ℝ} (hxc : x ≤ c)
    (hroot : ∀ y ∈ Icc x c, P.eval y ≠ 0)
    (hslope : ∀ y ∈ Icc x c, P.derivative.eval y / P.eval y ≤ -L) :
    L * (c - x) ≤ Real.log |P.eval x| - Real.log |P.eval c| := by
  have hd : ∀ y ∈ Icc x c,
      HasDerivAt (fun z => Real.log |P.eval z|) (P.derivative.eval y / P.eval y) y :=
    fun y hy => hasDerivAt_log_abs_eval P (hroot y hy)
  have h := (convex_Icc x c).image_sub_le_mul_sub_of_deriv_le
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    (fun y hy => by rw [(hd y (interior_subset hy)).deriv]; exact hslope y (interior_subset hy))
    x ⟨le_rfl, hxc⟩ c ⟨hxc, le_rfl⟩ hxc
  linarith

/-- Actual full nodal gain against the complex pole, on a rightward band.
The inverse-square sum still includes every indexed original node. -/
theorem right_band_gain {ι : Type*} (s : Finset ι) (nodes : ι → ℝ)
    (c α h L : ℝ) (hL : 0 ≤ L) (x : ℝ) (hx : c + h ≤ x) (hcx : c ≤ x)
    (hroot : ∀ y ∈ Icc c x, ∀ i ∈ s, y ≠ nodes i)
    (hslope : ∀ y ∈ Icc c x,
      L ≤ (Lagrange.nodal s nodes).derivative.eval y / (Lagrange.nodal s nodes).eval y) :
    L * h - (α ^ 2 / 2) * ∑ i ∈ s, 1 / (c - nodes i) ^ 2 ≤
      Real.log |(Lagrange.nodal s nodes).eval x| -
      Real.log ‖(Lagrange.nodal s nodes).eval₂ Complex.ofRealHom
        ((c : ℂ) + (α : ℂ) * Complex.I)‖ := by
  have hreal := real_gain_of_lower_slope (Lagrange.nodal s nodes) hcx
    (fun y hy => Lagrange.eval_nodal_not_at_node (hroot y hy)) hslope
  have hvertical := FullNodalVerticalIncrement.full_nodal_increment_le s nodes c α
    (hroot c ⟨le_rfl, hcx⟩)
  have hdist : L * h ≤ L * (x - c) := mul_le_mul_of_nonneg_left (by linarith) hL
  linarith

/-- Actual full nodal gain against the complex pole on a leftward band. -/
theorem left_band_gain {ι : Type*} (s : Finset ι) (nodes : ι → ℝ)
    (c α h L : ℝ) (hL : 0 ≤ L) (x : ℝ) (hx : x ≤ c - h) (hxc : x ≤ c)
    (hroot : ∀ y ∈ Icc x c, ∀ i ∈ s, y ≠ nodes i)
    (hslope : ∀ y ∈ Icc x c,
      (Lagrange.nodal s nodes).derivative.eval y / (Lagrange.nodal s nodes).eval y ≤ -L) :
    L * h - (α ^ 2 / 2) * ∑ i ∈ s, 1 / (c - nodes i) ^ 2 ≤
      Real.log |(Lagrange.nodal s nodes).eval x| -
      Real.log ‖(Lagrange.nodal s nodes).eval₂ Complex.ofRealHom
        ((c : ℂ) + (α : ℂ) * Complex.I)‖ := by
  have hreal := real_gain_of_upper_slope (Lagrange.nodal s nodes) hxc
    (fun y hy => Lagrange.eval_nodal_not_at_node (hroot y hy)) hslope
  have hvertical := FullNodalVerticalIncrement.full_nodal_increment_le s nodes c α
    (hroot c ⟨hxc, le_rfl⟩)
  have hdist : L * h ≤ L * (c - x) := mul_le_mul_of_nonneg_left (by linarith) hL
  linarith


end
end Jig133.FullNodalBandGain
end File_FullNodalBandGain

section File_FullProductLocalBand

/-!
# Local band propagation for the actual full real polynomial

The index type enumerates every complex root with its multiplicity. No
original factor, nonreal multiplier root or leading coefficient is discarded.
-/

noncomputable section
open Set Polynomial
open scoped BigOperators
namespace Jig133.FullProductLocalBand
local instance : DecidableEq ℂ := Classical.decEq _

abbrev RootIndex (P : ℝ[X]) : Type := (P.map Complex.ofRealHom).roots

def root (P : ℝ[X]) (i : RootIndex P) : ℂ := i

theorem root_index_card (P : ℝ[X]) : Fintype.card (RootIndex P) = P.natDegree := by
  rw [Multiset.card_coe, ← (IsAlgClosed.splits (P.map Complex.ofRealHom)).natDegree_eq_card_roots]
  exact Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective P

theorem sum_roots (P : ℝ[X]) {β : Type*} [AddCommMonoid β] (f : ℂ → β) :
    (∑ i : RootIndex P, f (root P i)) = ((P.map Complex.ofRealHom).roots.map f).sum := by
  simp only [root, Finset.sum_eq_multiset_sum, Multiset.map_univ]

theorem eval_complex (P : ℝ[X]) (x : ℝ) :
    (P.map Complex.ofRealHom).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) :=
  Polynomial.eval_map_apply Complex.ofRealHom x

theorem log_derivative_eq_slope (P : ℝ[X]) {x : ℝ} (hx : P.eval x ≠ 0) :
    P.derivative.eval x / P.eval x = ComplexRootStability.slope (root P) x := by
  have hc : (P.map Complex.ofRealHom).eval (x : ℂ) ≠ 0 := by
    rw [eval_complex]
    exact_mod_cast hx
  have he := (IsAlgClosed.splits (P.map Complex.ofRealHom)).eval_derivative_div_eval_of_ne_zero hc
  rw [← sum_roots P (fun z => 1 / ((x : ℂ) - z))] at he
  have hh := congrArg Complex.re he
  simpa only [Polynomial.derivative_map, eval_complex, ← Complex.ofReal_div,
    Complex.ofReal_re, Complex.re_sum, one_div, ComplexRootStability.slope] using hh

theorem eval_ne_zero_of_clearance (P : ℝ[X]) (hP : P ≠ 0)
    (q x δ : ℝ) (hδ : 0 < δ)
    (hclear : ∀ i, δ ≤ |q - (root P i).re|) (hx : |x - q| ≤ δ / 2) :
    P.eval x ≠ 0 := by
  intro hz
  have hmem : (x : ℂ) ∈ (P.map Complex.ofRealHom).roots := by
    apply (Polynomial.mem_roots (Polynomial.map_ne_zero hP)).mpr
    rw [Polynomial.IsRoot, eval_complex, hz, Complex.ofReal_zero]
  let i : RootIndex P := ⟨(x : ℂ), ⟨0, Multiset.count_pos.mpr hmem⟩⟩
  have hc := ComplexRootStability.denominator_comparison (root P i) q x δ (hclear i) hx
  have hzero : ‖(x : ℂ) - root P i‖ = 0 := by simp [root, i]
  rw [hzero] at hc
  linarith

/-- A center slope bound and actual all-root count control propagate to the full window. -/
theorem log_variation_le (P : ℝ[X]) (hP : P ≠ 0) (q δ a A L : ℝ)
    (hδ : 0 < δ) (ha : 0 ≤ a) (hasmall : a ≤ δ / 2) (hA : 0 ≤ A)
    (hclear : ∀ i, δ ≤ |q - (root P i).re|)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i : RootIndex P => |q - (root P i).re| ≤ r)).card : ℝ) ≤ A * r)
    (hcenter : |P.derivative.eval q / P.eval q| ≤ L)
    (x : ℝ) (hx : |x - q| ≤ a) :
    |Real.log (|P.eval x|) - Real.log (|P.eval q|)| ≤ (L + 8 * A * a / δ) * a := by
  have hq : P.eval q ≠ 0 := eval_ne_zero_of_clearance P hP q q δ hδ hclear
    (by simp; positivity)
  have hL : 0 ≤ L := (abs_nonneg _).trans hcenter
  have hK : 0 ≤ L + 8 * A * a / δ := by positivity
  have hbound : ∀ y ∈ Icc (q - a) (q + a),
      |P.derivative.eval y / P.eval y| ≤ L + 8 * A * a / δ := by
    intro y hy
    have hnear : |y - q| ≤ a := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hy0 := eval_ne_zero_of_clearance P hP q y δ hδ hclear (hnear.trans hasmall)
    have hs := ComplexRootStability.slope_change_le (root P) q y δ A hδ hclear hcount
      (hnear.trans hasmall)
    rw [← log_derivative_eq_slope P hy0, ← log_derivative_eq_slope P hq] at hs
    have hs' : |P.derivative.eval y / P.eval y - P.derivative.eval q / P.eval q| ≤
        (8 * A / δ) * a := hs.trans (mul_le_mul_of_nonneg_left hnear (by positivity))
    have ht := abs_add_le (P.derivative.eval y / P.eval y - P.derivative.eval q / P.eval q)
      (P.derivative.eval q / P.eval q)
    simp only [sub_add_cancel] at ht
    have heq : (8 * A / δ) * a = 8 * A * a / δ := by ring
    rw [heq] at hs'
    linarith
  have hd : ∀ y ∈ Icc (q - a) (q + a),
      HasDerivAt (fun z => Real.log (|P.eval z|)) (P.derivative.eval y / P.eval y) y := by
    intro y hy
    apply FullNodalBandGain.hasDerivAt_log_abs_eval
    apply eval_ne_zero_of_clearance P hP q y δ hδ hclear
    apply le_trans _ hasmall
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt)
    (fun y hy => by simpa only [Real.norm_eq_abs] using hbound y hy)
    (convex_Icc (q - a) (q + a))
    (show q ∈ Icc (q - a) (q + a) by constructor <;> linarith)
    (show x ∈ Icc (q - a) (q + a) by
      have hh := abs_le.mp hx
      constructor <;> linarith [hh.1, hh.2])
  have hm : |Real.log (|P.eval x|) - Real.log (|P.eval q|)| ≤
      (L + 8 * A * a / δ) * |x - q| := by
    simpa only [Real.norm_eq_abs] using hmean
  exact hm.trans (mul_le_mul_of_nonneg_left hx hK)

end Jig133.FullProductLocalBand

end
end File_FullProductLocalBand

section File_FullProductBandScale

/-!
# A uniform microscopic width for the full-product band

One positive width is fixed by the clearance, density and slope constants.
The elementary choice below is smaller than the square-root choice on paper.
-/

noncomputable section
open Set Polynomial
namespace Jig133.FullProductBandScale
open FullProductLocalBand

def width (c B L : ℝ) : ℝ := min (c / 4) (min (1 / (4 * L)) (min (c / (64 * B)) (1 / 16)))

theorem width_bounds {c B L : ℝ} (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) :
    0 < width c B L ∧ width c B L ≤ c / 4 ∧ width c B L ≤ 1 / 16 ∧
      L * width c B L + 16 * B * (width c B L) ^ 2 / c ≤ 1 / 2 := by
  let a := width c B L
  have ha : 0 < a := by dsimp [a, width]; positivity
  have hac : a ≤ c / 4 := min_le_left _ _
  have haL : a ≤ 1 / (4 * L) := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a ≤ c / (64 * B) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLa : L * a ≤ 1 / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * L)).mp haL
    nlinarith
  have hBa : 16 * B * a ^ 2 / c ≤ 1 / 4 := by
    apply (div_le_iff₀ hc).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 64 * B)).mp haB
    have hs : a ^ 2 ≤ a := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16 * B)
    nlinarith
  exact ⟨ha, hac, ha1, by linarith⟩

theorem local_log_bound (P : ℝ[X]) (hP : P ≠ 0) (n : ℕ) (hn : 0 < n)
    (q c B L : ℝ) (hc : 0 < c) (hB : 0 < B) (hL : 0 < L)
    (hclear : ∀ i, c / n ≤ |q - (root P i).re|)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i : RootIndex P => |q - (root P i).re| ≤ r)).card : ℝ) ≤
        2 * B * n * r)
    (hcenter : |P.derivative.eval q / P.eval q| ≤ L * n)
    (x : ℝ) (hx : |x - q| ≤ width c B L / n) :
    P.eval x ≠ 0 ∧ (∀ i, (c - width c B L) / n ≤ |x - (root P i).re|) ∧
      |Real.log (|P.eval x|) - Real.log (|P.eval q|)| ≤ 1 / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨ha, hac, _, hcost⟩ := width_bounds hc hB hL
  have hsmall : width c B L / n ≤ (c / n) / 2 := by
    have hh : width c B L ≤ c / 2 := by linarith
    have hb := div_le_div_of_nonneg_right hh hnR.le
    calc
      width c B L / n ≤ (c / 2) / n := hb
      _ = (c / n) / 2 := by ring
  refine ⟨eval_ne_zero_of_clearance P hP q x (c / n) (div_pos hc hnR)
    hclear (hx.trans hsmall), ?_, ?_⟩
  · intro i
    have hh := ComplexRootStability.projected_clearance (root P i) q x
      (c / n) (width c B L / n) (hclear i) hx
    simpa only [sub_div] using hh
  · have hh := log_variation_le P hP q (c / n) (width c B L / n)
      (2 * B * n) (L * n) (div_pos hc hnR) (by positivity) hsmall (by positivity)
      hclear hcount hcenter x hx
    have he : (L * n + 8 * (2 * B * n) * (width c B L / n) / (c / n)) *
        (width c B L / n) = L * width c B L + 16 * B * (width c B L) ^ 2 / c := by
      field_simp [hc.ne', hnR.ne']
      ring
    rw [he] at hh
    exact hh.trans hcost

theorem band_from_log_bound (P : ℝ[X]) {q x η T A : ℝ}
    (hq : P.eval q ≠ 0) (hx : P.eval x ≠ 0)
    (hband : η * A ≤ |P.eval q| ∧ |P.eval q| ≤ T * A)
    (hlog : |Real.log (|P.eval x|) - Real.log (|P.eval q|)| ≤ 1 / 2) :
    (η * Real.exp (-(1 / 2 : ℝ))) * A ≤ |P.eval x| ∧
      |P.eval x| ≤ (T * Real.exp (1 / 2 : ℝ)) * A := by
  have hlogs := abs_le.mp hlog
  have hlo : Real.log (|P.eval q|) + (-(1 / 2 : ℝ)) ≤ Real.log (|P.eval x|) := by linarith
  have hhi : Real.log (|P.eval x|) ≤ Real.log (|P.eval q|) + (1 / 2 : ℝ) := by linarith
  have hel := Real.exp_le_exp.mpr hlo
  have heh := Real.exp_le_exp.mpr hhi
  rw [Real.exp_add, Real.exp_log (abs_pos.mpr hq), Real.exp_log (abs_pos.mpr hx)] at hel
  rw [Real.exp_add, Real.exp_log (abs_pos.mpr hq), Real.exp_log (abs_pos.mpr hx)] at heh
  constructor
  · have hh := mul_le_mul_of_nonneg_right hband.1 (Real.exp_pos (-(1 / 2 : ℝ))).le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hband.2 (Real.exp_pos (1 / 2 : ℝ)).le
    nlinarith

end Jig133.FullProductBandScale

end
end File_FullProductBandScale

section File_FiniteMeasureMaximalDensity

/-!
# A genuine global maximal-density bound for a finite measure on the line

The family consists of all positive-radius density witnesses. Its radii are
bounded by the actual finite mass. The proved abstract Vitali construction with
size factor 2 produces a disjoint family; its threefold dilations cover every
witness center. No cover is an input. Closed balls retain endpoint atoms.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace Jig133.FiniteMeasureMaximalDensity

/-- Every pair is an actual center and positive-radius density witness. -/
def witnesses (σ : Measure ℝ) (L : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ ENNReal.ofReal (L * (2 * p.2)) < σ (closedBall p.1 p.2)}

/-- The global strict superlevel set of the centered, length-normalized density. -/
def maximalSet (σ : Measure ℝ) (L : ℝ) : Set ℝ :=
  {x | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (L * (2 * r)) < σ (closedBall x r)}

variable (σ : Measure ℝ) [IsFiniteMeasure σ]

theorem witness_real_bound (L : ℝ) (hL : 0 < L) (p : ℝ × ℝ)
    (hp : p ∈ witnesses σ L) :
    L * (2 * p.2) < σ.real (closedBall p.1 p.2) := by
  have hnonneg : 0 ≤ L * (2 * p.2) :=
    mul_nonneg hL.le (mul_nonneg (by norm_num) hp.1.le)
  exact (ENNReal.ofReal_lt_iff_lt_toReal hnonneg (measure_ne_top σ _)).mp hp.2

/-- Finiteness bounds the radii of all witnesses, with no support assumption. -/
theorem witness_radius_bound (L : ℝ) (hL : 0 < L) (p : ℝ × ℝ)
    (hp : p ∈ witnesses σ L) : p.2 ≤ σ.real univ / (2 * L) := by
  have hw := witness_real_bound σ L hL p hp
  have hm : σ.real (closedBall p.1 p.2) ≤ σ.real univ :=
    measureReal_mono (subset_univ _)
  apply (le_div_iff₀ (mul_pos (by norm_num) hL)).mpr
  nlinarith

/-- An actually constructed disjoint countable witness family whose threefold
dilations cover every witness center. The abstract Vitali size factor is 2 > 1;
no use is made of the closed-ball covering theorem at its invalid endpoint 3. -/
theorem exists_disjoint_countable_cover (L : ℝ) (hL : 0 < L) :
    ∃ u : Set (ℝ × ℝ), u ⊆ witnesses σ L ∧ u.Countable ∧
      (u.PairwiseDisjoint fun p => closedBall p.1 p.2) ∧
      maximalSet σ L ⊆ ⋃ p ∈ u, closedBall p.1 (3 * p.2) := by
  classical
  obtain ⟨u, hu, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun p : ℝ × ℝ => closedBall p.1 p.2) (witnesses σ L) (fun p => p.2)
      2 (by norm_num) (fun p hp => hp.1.le)
      (σ.real univ / (2 * L)) (fun p hp => witness_radius_bound σ L hL p hp)
      (fun p hp => ⟨p.1, mem_closedBall_self hp.1.le⟩)
  have hcount : u.Countable := hdisj.countable_of_nonempty_interior (by
    intro p hp
    exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (hu hp).1)⟩)
  refine ⟨u, hu, hcount, hdisj, ?_⟩
  intro x hx
  obtain ⟨r, hr, hd⟩ := hx
  obtain ⟨p, hp, hinter, hsize⟩ := hcover (x, r) ⟨hr, hd⟩
  have hdist : dist x p.1 ≤ r + p.2 :=
    dist_le_add_of_nonempty_closedBall_inter_closedBall hinter
  have hmem : x ∈ closedBall p.1 (3 * p.2) := by
    rw [mem_closedBall]
    linarith
  exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, hmem⟩⟩

/-- Each selected dilation is paid for by the actual mass of its original ball. -/
theorem three_dilate_volume_le (L : ℝ) (hL : 0 < L) (p : ℝ × ℝ)
    (hp : p ∈ witnesses σ L) :
    volume (closedBall p.1 (3 * p.2)) ≤
      ENNReal.ofReal (3 / L) * σ (closedBall p.1 p.2) := by
  have hw := witness_real_bound σ L hL p hp
  have hc : 0 ≤ (3 : ℝ) / L := div_nonneg (by norm_num) hL.le
  have hreal : 2 * (3 * p.2) ≤ (3 * σ.real (closedBall p.1 p.2)) / L := by
    apply (le_div_iff₀ hL).mpr
    nlinarith
  calc
    _ = ENNReal.ofReal (2 * (3 * p.2)) := Real.volume_closedBall _ _
    _ ≤ ENNReal.ofReal ((3 * σ.real (closedBall p.1 p.2)) / L) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (3 / L) * σ (closedBall p.1 p.2) := by
      rw [show (3 * σ.real (closedBall p.1 p.2)) / L =
        (3 / L) * σ.real (closedBall p.1 p.2) by ring]
      rw [ENNReal.ofReal_mul hc, ofReal_measureReal]

/-- The global estimate is obtained from the constructed cover and disjoint
mass sum. No measurability of the superlevel set is needed for this outer bound. -/
theorem maximalSet_volume_le_three (L : ℝ) (hL : 0 < L) :
    volume (maximalSet σ L) ≤ ENNReal.ofReal (3 * σ.real univ / L) := by
  classical
  obtain ⟨u, hu, hcount, hdisj, hcover⟩ := exists_disjoint_countable_cover σ L hL
  have hmass : (∑' p : u, σ (closedBall p.val.1 p.val.2)) ≤ σ univ := by
    rw [← measure_biUnion hcount hdisj (fun p _ => isClosed_closedBall.measurableSet)]
    exact measure_mono (subset_univ _)
  have hc : 0 ≤ (3 : ℝ) / L := div_nonneg (by norm_num) hL.le
  calc
    volume (maximalSet σ L) ≤ volume (⋃ p ∈ u, closedBall p.1 (3 * p.2)) :=
      measure_mono hcover
    _ ≤ ∑' p : u, volume (closedBall p.val.1 (3 * p.val.2)) :=
      measure_biUnion_le volume hcount _
    _ ≤ ∑' p : u, ENNReal.ofReal (3 / L) * σ (closedBall p.val.1 p.val.2) :=
      ENNReal.tsum_le_tsum (fun p => three_dilate_volume_le σ L hL p.val (hu p.property))
    _ = ENNReal.ofReal (3 / L) * ∑' p : u, σ (closedBall p.val.1 p.val.2) :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (3 / L) * σ univ := mul_le_mul_right hmass _
    _ = ENNReal.ofReal ((3 / L) * σ.real univ) := by
      rw [ENNReal.ofReal_mul hc, ofReal_measureReal]
    _ = ENNReal.ofReal (3 * σ.real univ / L) := by congr 1; ring

/-- Literal closed-interval form with the proved normalized constant 3. -/
theorem maximal_density_bound_three (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (L * (2 * r)) < σ (Icc (x - r) (x + r))} ≤
      ENNReal.ofReal (3 * σ.real univ / L) := by
  simpa only [maximalSet, Real.closedBall_eq_Icc] using maximalSet_volume_le_three σ L hL

/-- Literal closed-interval form, with the stronger proved constant 4. -/
theorem maximal_density_bound_four (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (L * (2 * r)) < σ (Icc (x - r) (x + r))} ≤
      ENNReal.ofReal (4 * σ.real univ / L) := by
  apply (maximal_density_bound_three σ L hL).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hL.le
  have hm : 0 ≤ σ.real univ := measureReal_nonneg
  nlinarith

/-- The requested length-normalized constant-6 bound. -/
theorem maximal_density_bound (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (L * (2 * r)) < σ (Icc (x - r) (x + r))} ≤
      ENNReal.ofReal (6 * σ.real univ / L) := by
  apply (maximal_density_bound_four σ L hL).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hL.le
  have hm : 0 ≤ σ.real univ := measureReal_nonneg
  nlinarith

/-- The paper's unnormalized density σ([x-r,x+r])/r has weak constant 6.
The factor two is explicit; this preserves the saved paper deletion constants. -/
theorem unnormalized_maximal_density_bound (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (L * r) < σ (Icc (x - r) (x + r))} ≤
      ENNReal.ofReal (6 * σ.real univ / L) := by
  have h := maximal_density_bound_three σ (L / 2) (div_pos hL (by norm_num))
  have hfactor (r : ℝ) : (L / 2) * (2 * r) = L * r := by ring
  have hconstant : 3 * σ.real univ / (L / 2) = 6 * σ.real univ / L := by
    rw [div_div_eq_mul_div]
    ring
  simpa only [hfactor, hconstant] using h

end Jig133.FiniteMeasureMaximalDensity

end
end File_FiniteMeasureMaximalDensity

section File_FiniteRootDensity

/-!
# Full indexed-root density and whole bad-cell deletion

The measure sums one Dirac mass for every original index. Repeated node values
retain their full multiplicities. Every point of a bad center's radius-4h cell
is an actual unnormalized density witness after enlarging its witness radius.
The finite-measure maximal bound therefore controls the entire bad-cell union.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Jig133.FiniteRootDensity

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

/-- Counting measure of all original indices, without merging repeated nodes. -/
def indexedMeasure (nodes : ι → ℝ) : Measure ℝ :=
  ∑ i, Measure.dirac (nodes i)

instance finite_indexedMeasure (nodes : ι → ℝ) : IsFiniteMeasure (indexedMeasure nodes) := by
  unfold indexedMeasure
  infer_instance

/-- The closed-radius count, with original index multiplicities. -/
def count (nodes : ι → ℝ) (c r : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => |c - nodes i| ≤ r)).card

theorem indexedMeasure_apply (nodes : ι → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    indexedMeasure nodes s =
      ((Finset.univ.filter (fun i => nodes i ∈ s)).card : ℝ≥0∞) := by
  classical
  simp only [indexedMeasure, Measure.finsetSum_apply, Measure.dirac_apply' _ hs,
    Set.indicator_apply, Pi.one_apply, Finset.sum_boole]

theorem indexedMeasure_univ (nodes : ι → ℝ) :
    indexedMeasure nodes univ = (Fintype.card ι : ℝ≥0∞) := by
  classical
  simpa only [mem_univ, Finset.filter_true, Finset.card_univ] using
    indexedMeasure_apply nodes univ MeasurableSet.univ

theorem indexedMeasure_real_univ (nodes : ι → ℝ) :
    (indexedMeasure nodes).real univ = (Fintype.card ι : ℝ) := by
  rw [Measure.real, indexedMeasure_univ, ENNReal.toReal_natCast]

theorem mem_centered_interval_iff (x c r : ℝ) :
    x ∈ Icc (c - r) (c + r) ↔ |c - x| ≤ r := by
  rw [mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem indexedMeasure_Icc (nodes : ι → ℝ) (c r : ℝ) :
    indexedMeasure nodes (Icc (c - r) (c + r)) = (count nodes c r : ℝ≥0∞) := by
  classical
  simpa only [count, mem_centered_interval_iff] using
    indexedMeasure_apply nodes (Icc (c - r) (c + r)) measurableSet_Icc

theorem indexedMeasure_real_Icc (nodes : ι → ℝ) (c r : ℝ) :
    (indexedMeasure nodes).real (Icc (c - r) (c + r)) = (count nodes c r : ℝ) := by
  rw [Measure.real, indexedMeasure_Icc, ENNReal.toReal_natCast]

theorem count_pos_iff (nodes : ι → ℝ) (c r : ℝ) :
    0 < count nodes c r ↔ ∃ i, |c - nodes i| ≤ r := by
  classical
  rw [count, Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- The literal unnormalized density set of the complete index family. -/
def densitySet (nodes : ι → ℝ) (L : ℝ) : Set ℝ :=
  {x | ∃ r : ℝ, 0 < r ∧ L * r < (count nodes x r : ℝ)}

theorem densitySet_volume_le (nodes : ι → ℝ) (L : ℝ) (hL : 0 < L) :
    volume (densitySet nodes L) ≤ ENNReal.ofReal (6 * (Fintype.card ι : ℝ) / L) := by
  have hsubset : densitySet nodes L ⊆ {x : ℝ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (L * r) < indexedMeasure nodes (Icc (x - r) (x + r))} := by
    rintro x ⟨r, hr, hd⟩
    refine ⟨r, hr, ?_⟩
    rw [indexedMeasure_Icc, ← ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hL.le hr.le)).mpr hd
  calc
    volume (densitySet nodes L) ≤ volume {x : ℝ | ∃ r : ℝ, 0 < r ∧
        ENNReal.ofReal (L * r) < indexedMeasure nodes (Icc (x - r) (x + r))} :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal (6 * (indexedMeasure nodes).real univ / L) :=
      FiniteMeasureMaximalDensity.unnormalized_maximal_density_bound
        (indexedMeasure nodes) L hL
    _ = ENNReal.ofReal (6 * (Fintype.card ι : ℝ) / L) := by
      rw [indexedMeasure_real_univ]

/-- A center is bad when its actual length-normalized count exceeds B times
the number of original indices. The witness radius is part of the definition. -/
def badCenter (nodes : ι → ℝ) (B c : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ 2 * B * (Fintype.card ι : ℝ) * r < (count nodes c r : ℝ)

theorem density_witness_index (nodes : ι → ℝ) (B c r : ℝ) (hB : 0 < B) (hr : 0 < r)
    (hd : 2 * B * (Fintype.card ι : ℝ) * r < (count nodes c r : ℝ)) :
    ∃ i, |c - nodes i| ≤ r := by
  have hnonneg : 0 ≤ 2 * B * (Fintype.card ι : ℝ) * r :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB.le) (Nat.cast_nonneg _)) hr.le
  have hpos : 0 < count nodes c r := by
    exact_mod_cast (lt_of_le_of_lt hnonneg hd)
  exact (count_pos_iff nodes c r).mp hpos

/-- Weak radius-4h avoidance implies the weak radius bound, which suffices for
the enlargement argument even when a root is exactly on the cell boundary. -/
theorem bad_radius_le (nodes : ι → ℝ) (B h c r : ℝ) (hB : 0 < B) (hr : 0 < r)
    (havoid : ∀ i, 4 * h ≤ |c - nodes i|)
    (hd : 2 * B * (Fintype.card ι : ℝ) * r < (count nodes c r : ℝ)) :
    4 * h ≤ r := by
  obtain ⟨i, hi⟩ := density_witness_index nodes B c r hB hr hd
  exact (havoid i).trans hi

/-- Strict avoidance of the closed cell gives the strict radius statement. -/
theorem bad_radius_gt (nodes : ι → ℝ) (B h c r : ℝ) (hB : 0 < B) (hr : 0 < r)
    (havoid : ∀ i, 4 * h < |c - nodes i|)
    (hd : 2 * B * (Fintype.card ι : ℝ) * r < (count nodes c r : ℝ)) :
    4 * h < r := by
  obtain ⟨i, hi⟩ := density_witness_index nodes B c r hB hr hd
  exact (havoid i).trans_le hi

/-- Every original witness index survives translation and radius enlargement. -/
theorem count_le_shifted (nodes : ι → ℝ) (c x r d : ℝ) (hx : |x - c| ≤ d) :
    count nodes c r ≤ count nodes x (r + d) := by
  classical
  unfold count
  apply Finset.card_le_card
  intro i hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
  calc
    |x - nodes i| ≤ |x - c| + |c - nodes i| := abs_sub_le x c (nodes i)
    _ ≤ d + r := add_le_add hx (Finset.mem_filter.mp hi).2
    _ = r + d := add_comm _ _

/-- The whole cell, not merely its center, lies in a genuine density superlevel
set: use the explicit radius R = r + 4h, with R ≤ 2r. -/
theorem bad_cell_mem_densitySet (nodes : ι → ℝ) (B h c x : ℝ)
    (hB : 0 < B) (hh : 0 < h) (havoid : ∀ i, 4 * h ≤ |c - nodes i|)
    (hbad : badCenter nodes B c) (hx : |x - c| ≤ 4 * h) :
    x ∈ densitySet nodes (B * (Fintype.card ι : ℝ)) := by
  obtain ⟨r, hr, hd⟩ := hbad
  have hrad := bad_radius_le nodes B h c r hB hr havoid hd
  have hcount : (count nodes c r : ℝ) ≤ (count nodes x (r + 4 * h) : ℝ) := by
    exact_mod_cast count_le_shifted nodes c x r (4 * h) hx
  have hscale : (B * (Fintype.card ι : ℝ)) * (r + 4 * h) ≤
      2 * B * (Fintype.card ι : ℝ) * r := by
    calc
      _ ≤ (B * (Fintype.card ι : ℝ)) * (2 * r) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hB.le (Nat.cast_nonneg _))
      _ = _ := by ring
  exact ⟨r + 4 * h, add_pos hr (mul_pos (by norm_num) hh),
    lt_of_le_of_lt hscale (lt_of_lt_of_le hd hcount)⟩

/-- The bad subfamily is obtained by filtering the given finite centers. -/
def badCenters (nodes : ι → ℝ) (centers : Finset ℝ) (B : ℝ) : Finset ℝ := by
  classical
  exact centers.filter (badCenter nodes B)

/-- Literal union of the complete closed radius-4h cells at bad centers. -/
def badCells (nodes : ι → ℝ) (centers : Finset ℝ) (B h : ℝ) : Set ℝ :=
  ⋃ c ∈ badCenters nodes centers B, Icc (c - 4 * h) (c + 4 * h)

theorem badCells_subset_densitySet (nodes : ι → ℝ) (centers : Finset ℝ) (B h : ℝ)
    (hB : 0 < B) (hh : 0 < h)
    (havoid : ∀ c ∈ centers, ∀ i, 4 * h ≤ |c - nodes i|) :
    badCells nodes centers B h ⊆ densitySet nodes (B * (Fintype.card ι : ℝ)) := by
  classical
  intro x hx
  obtain ⟨c, hcx⟩ := mem_iUnion.mp hx
  obtain ⟨hc, hx⟩ := mem_iUnion.mp hcx
  have hc' : c ∈ centers ∧ badCenter nodes B c := by
    simpa only [badCenters, Finset.mem_filter] using hc
  have hx' : |x - c| ≤ 4 * h := by
    rw [abs_sub_comm]
    exact (mem_centered_interval_iff x c (4 * h)).mp hx
  exact bad_cell_mem_densitySet nodes B h c x hB hh (havoid c hc'.1) hc'.2 hx'

/-- A bound for the full bad-cell union with all original multiplicities.
No separation, sorting, bounded support or supplied cover is assumed. -/
theorem badCells_volume_le (nodes : ι → ℝ) (centers : Finset ℝ) (B h : ℝ)
    (hn : 0 < Fintype.card ι) (hB : 0 < B) (hh : 0 < h)
    (havoid : ∀ c ∈ centers, ∀ i, 4 * h ≤ |c - nodes i|) :
    volume (badCells nodes centers B h) ≤ ENNReal.ofReal (6 / B) := by
  have hnreal : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  calc
    volume (badCells nodes centers B h) ≤
        volume (densitySet nodes (B * (Fintype.card ι : ℝ))) :=
      measure_mono (badCells_subset_densitySet nodes centers B h hB hh havoid)
    _ ≤ ENNReal.ofReal (6 * (Fintype.card ι : ℝ) / (B * (Fintype.card ι : ℝ))) :=
      densitySet_volume_le nodes _ (mul_pos hB hnreal)
    _ = ENNReal.ofReal (6 / B) := by
      rw [mul_div_mul_right 6 B hnreal.ne']

end Jig133.FiniteRootDensity

end
end File_FiniteRootDensity

section File_FullProductProjectedFilter

/-!
# Actual projected-root exclusion sets for the full polynomial

The density and clearance cutoffs use every complex root with multiplicity.
Only these geometric filters project roots to the real line.
-/

noncomputable section
open Set MeasureTheory Polynomial
open scoped ENNReal BigOperators
namespace Jig133.FullProductProjectedFilter
open FullProductLocalBand

def projected (P : ℝ[X]) (i : RootIndex P) : ℝ := (root P i).re

def near (P : ℝ[X]) (c : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i : RootIndex P, Icc (projected P i - c / n) (projected P i + c / n)

def bad (P : ℝ[X]) (c B : ℝ) (n : ℕ) : Set ℝ :=
  FiniteRootDensity.densitySet (projected P) (2 * B * n) ∪ near P c n

theorem near_volume_le (P : ℝ[X]) (c : ℝ) (n : ℕ) :
    volume (near P c n) ≤ ENNReal.ofReal ((P.natDegree : ℝ) * (2 * c / n)) := by
  calc
    _ ≤ ∑' i : RootIndex P,
        volume (Icc (projected P i - c / n) (projected P i + c / n)) := measure_iUnion_le _
    _ = ∑ i : RootIndex P, ENNReal.ofReal (2 * c / n) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.volume_Icc]
      congr 1
      ring
    _ = (Fintype.card (RootIndex P) : ℝ≥0∞) * ENNReal.ofReal (2 * c / n) := by simp
    _ = _ := by
      rw [root_index_card, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ P.natDegree)]

theorem bad_volume_le (P : ℝ[X]) (c B : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hB : 0 < B) (hn : 0 < n) (hdeg : P.natDegree ≤ 2 * n) :
    volume (bad P c B n) ≤ ENNReal.ofReal (6 / B + 4 * c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (P.natDegree : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hdeg
  have hden : 0 < 2 * B * (n : ℝ) := by positivity
  have hcount := FiniteRootDensity.densitySet_volume_le (projected P) (2 * B * n) hden
  rw [root_index_card] at hcount
  have hdensity : volume (FiniteRootDensity.densitySet (projected P) (2 * B * n)) ≤
      ENNReal.ofReal (6 / B) := by
    apply hcount.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      6 * (P.natDegree : ℝ) / (2 * B * n) ≤ 6 * (2 * (n : ℝ)) / (2 * B * n) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) hden.le
      _ = 6 / B := by field_simp
  have hnear : volume (near P c n) ≤ ENNReal.ofReal (4 * c) := by
    apply (near_volume_le P c n).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      (P.natDegree : ℝ) * (2 * c / n) ≤ (2 * (n : ℝ)) * (2 * c / n) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ = 4 * c := by
        field_simp
        ring
  calc
    _ ≤ volume (FiniteRootDensity.densitySet (projected P) (2 * B * n)) +
        volume (near P c n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (6 / B) + ENNReal.ofReal (4 * c) := add_le_add hdensity hnear
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

theorem controls_of_not_mem (P : ℝ[X]) (c B x : ℝ) (n : ℕ)
    (hx : x ∉ bad P c B n) :
    (∀ i, c / n ≤ |x - (root P i).re|) ∧
    (∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun i : RootIndex P => |x - (root P i).re| ≤ r)).card : ℝ) ≤
        2 * B * n * r) := by
  constructor
  · intro i
    apply le_of_not_gt
    intro hi
    apply hx
    right
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    apply (FiniteRootDensity.mem_centered_interval_iff x (projected P i) (c / n)).mpr
    simpa only [projected, abs_sub_comm] using hi.le
  · intro r hr
    apply le_of_not_gt
    intro hh
    apply hx
    left
    exact ⟨r, hr, hh⟩

end Jig133.FullProductProjectedFilter

end
end File_FullProductProjectedFilter

section File_CayleyRootMeasure

/-!
# An actual positive Cayley root measure

The normalized angular measure is pushed forward by the real Cayley map.
Its probability mass and zero-scale Dirac case are proved directly. The
logarithmic identity below is pointwise off the two indicated factors and
then almost everywhere in the angular parameter. It does not yet assert
integrability or an integrated logarithmic-potential formula.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Jig133.CayleyRootMeasure

/-- Probability normalization of Lebesgue measure on one angular period. -/
def angular : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ •
    volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

instance angular_probability : IsProbabilityMeasure angular where
  measure_univ := by
    change (ENNReal.ofReal (2 * Real.pi))⁻¹ *
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) univ = 1
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.inv_mul_cancel
      (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne' ENNReal.ofReal_ne_top

theorem angular_finite : IsFiniteMeasure angular := inferInstance

def q (θ : ℝ) : ℂ := circleMap 0 1 θ

theorem measurable_q : Measurable q := measurable_circleMap 0 1

theorem norm_q (θ : ℝ) : ‖q θ‖ = 1 := by simp [q]

/-- Division is totalized at -1; the resulting function is still Borel. -/
def cayley (u : ℂ) : ℝ := (-Complex.I * (u - 1) / (u + 1)).re

theorem measurable_cayley : Measurable cayley := by
  change Measurable (fun u : ℂ => (-Complex.I * (u - 1) / (u + 1)).re)
  apply Complex.continuous_re.measurable.comp
  exact (measurable_const.mul (measurable_id.sub measurable_const)).div
    (measurable_id.add measurable_const)

def affineCayley (a s θ : ℝ) : ℝ := a + s * cayley (q θ)

theorem measurable_affineCayley (a s : ℝ) : Measurable (affineCayley a s) :=
  measurable_const.add (measurable_const.mul (measurable_cayley.comp measurable_q))

/-- The construction exists for every real scale. Positive scale is required
only in the upper-half-plane identities below. -/
def rootMeasure (a s : ℝ) : Measure ℝ := angular.map (affineCayley a s)

instance rootMeasure_probability (a s : ℝ) : IsProbabilityMeasure (rootMeasure a s) :=
  Measure.isProbabilityMeasure_map (measurable_affineCayley a s).aemeasurable

theorem rootMeasure_finite (a s : ℝ) : IsFiniteMeasure (rootMeasure a s) := inferInstance

theorem rootMeasure_mass (a s : ℝ) : rootMeasure a s univ = 1 := measure_univ

theorem rootMeasure_real_mass (a s : ℝ) : (rootMeasure a s).real univ = 1 :=
  probReal_univ

theorem rootMeasure_zero (a : ℝ) : rootMeasure a 0 = Measure.dirac a := by
  change angular.map (fun θ => a + 0 * cayley (q θ)) = Measure.dirac a
  simp only [zero_mul, add_zero, Measure.map_const, measure_univ, one_smul]

/-- Each fixed circle point has only a countable angular preimage. This proves
the needed null exceptions without assuming that the pushforward is atomless. -/
theorem ae_q_ne (u : ℂ) : ∀ᵐ θ ∂angular, q θ ≠ u := by
  have hc : {θ : ℝ | q θ = u}.Countable := by
    change (circleMap 0 1 ⁻¹' {u}).Countable
    exact (Set.countable_singleton u).preimage_circleMap 0 one_ne_zero
  have hv : ∀ᵐ θ ∂volume, q θ ≠ u := hc.ae_notMem volume
  exact Measure.ae_smul_measure (ae_restrict_of_ae hv) _

/-- Exact agreement with the existing circle average, for totalized integrals.
This normalization identity alone makes no integrability claim. -/
theorem integral_angular_eq_circleAverage (f : ℂ → ℝ) :
    (∫ θ, f (q θ) ∂angular) = Real.circleAverage f 0 1 := by
  simp only [angular, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal Real.two_pi_pos.le,
    Real.circleAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le, q]

/-- On the unit circle the rational Cayley value is real, including its
totalized value at the exceptional point -1. -/
theorem ofReal_cayley {u : ℂ} (hu : ‖u‖ = 1) :
    (cayley u : ℂ) = -Complex.I * (u - 1) / (u + 1) := by
  have hn : u.re * u.re + u.im * u.im = 1 := by
    calc
      _ = Complex.normSq u := (Complex.normSq_apply u).symm
      _ = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
      _ = 1 := by rw [hu]; norm_num
  have hi : (-Complex.I * (u - 1) / (u + 1)).im =
      (1 - u.re * u.re - u.im * u.im) / Complex.normSq (u + 1) := by
    rw [Complex.div_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im]
    ring
  apply Complex.ext
  · rfl
  · change 0 = (-Complex.I * (u - 1) / (u + 1)).im
    rw [hi, show 1 - u.re * u.re - u.im * u.im = 0 by linarith, zero_div]

def upperShift (a s : ℝ) (w : ℂ) : ℂ := w - (a : ℂ) + (s : ℂ) * Complex.I

def lowerShift (a s : ℝ) (w : ℂ) : ℂ := w - (a : ℂ) - (s : ℂ) * Complex.I

def diskPoint (a s : ℝ) (w : ℂ) : ℂ := -lowerShift a s w / upperShift a s w

theorem upperShift_ne_zero (a s : ℝ) (w : ℂ) (hs : 0 < s) (hw : 0 ≤ w.im) :
    upperShift a s w ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp [upperShift] at hi
  linarith

theorem shift_norm_sq_difference (a s : ℝ) (w : ℂ) :
    ‖upperShift a s w‖ ^ 2 - ‖lowerShift a s w‖ ^ 2 = 4 * s * w.im := by
  simp only [upperShift, lowerShift, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The transformed point lies in the closed unit disk, including real w. -/
theorem norm_diskPoint_le_one (a s : ℝ) (w : ℂ) (hs : 0 < s) (hw : 0 ≤ w.im) :
    ‖diskPoint a s w‖ ≤ 1 := by
  have hA : 0 < ‖upperShift a s w‖ := norm_pos_iff.mpr (upperShift_ne_zero a s w hs hw)
  have hsq : ‖lowerShift a s w‖ ^ 2 ≤ ‖upperShift a s w‖ ^ 2 := by
    have he := shift_norm_sq_difference a s w
    have hp : 0 ≤ 4 * s * w.im :=
      mul_nonneg (mul_nonneg (by norm_num) hs.le) hw
    linarith
  have hn := (sq_le_sq₀ (norm_nonneg (lowerShift a s w))
    (norm_nonneg (upperShift a s w))).mp hsq
  rw [diskPoint, norm_div, norm_neg]
  exact (div_le_iff₀ hA).mpr (by simpa only [one_mul] using hn)

/-- The actual rational identity, before applying any logarithm. -/
theorem cayley_factorization (a s : ℝ) (w u : ℂ)
    (hs : 0 < s) (hw : 0 ≤ w.im) (hu : ‖u‖ = 1) (hp : u + 1 ≠ 0) :
    w - ((a + s * cayley u : ℝ) : ℂ) =
      upperShift a s w * (u - diskPoint a s w) / (u + 1) := by
  rw [Complex.ofReal_add, Complex.ofReal_mul, ofReal_cayley hu]
  have hA := upperShift_ne_zero a s w hs hw
  dsimp only [diskPoint]
  field_simp [hp, hA]
  dsimp only [upperShift, lowerShift]
  ring

/-- Both logarithmic zero hazards are explicitly excluded before log_mul and
log_div are used; the upper factor is proved nonzero from hs and hw. -/
theorem log_norm_cayley (a s : ℝ) (w u : ℂ)
    (hs : 0 < s) (hw : 0 ≤ w.im) (hu : ‖u‖ = 1)
    (hp : u + 1 ≠ 0) (hr : u - diskPoint a s w ≠ 0) :
    Real.log ‖w - ((a + s * cayley u : ℝ) : ℂ)‖ =
      Real.log ‖upperShift a s w‖ + Real.log ‖u - diskPoint a s w‖ -
        Real.log ‖u + 1‖ := by
  have hA := norm_ne_zero_iff.mpr (upperShift_ne_zero a s w hs hw)
  have hP := norm_ne_zero_iff.mpr hp
  have hR := norm_ne_zero_iff.mpr hr
  rw [cayley_factorization a s w u hs hw hu hp, norm_div, norm_mul,
    Real.log_div (mul_ne_zero hA hR) hP, Real.log_mul hA hR]

/-- Genuine angular-a.e. identity for the literal pushforward parameter map.
The exceptional parameter set depends on w; no common null set is claimed. -/
theorem ae_log_norm_cayley (a s : ℝ) (w : ℂ) (hs : 0 < s) (hw : 0 ≤ w.im) :
    ∀ᵐ θ ∂angular,
      Real.log ‖w - (affineCayley a s θ : ℂ)‖ =
        Real.log ‖upperShift a s w‖ + Real.log ‖q θ - diskPoint a s w‖ -
          Real.log ‖q θ + 1‖ := by
  filter_upwards [ae_q_ne (-1), ae_q_ne (diskPoint a s w)] with θ hp hr
  have hp' : q θ + 1 ≠ 0 := by simpa only [sub_neg_eq_add] using (sub_ne_zero.mpr hp)
  exact log_norm_cayley a s w (q θ) hs hw (norm_q θ) hp' (sub_ne_zero.mpr hr)

end Jig133.CayleyRootMeasure

end
end File_CayleyRootMeasure

section File_CayleyRootPotential

/-!
# The integrated logarithmic potential of the actual Cayley probability

Circle logarithm integrability, the angular-a.e. rational identity, and the
measurable pushforward give genuine root-measure integrability before the
integral is evaluated. Nonnegative scales include the separate Dirac case.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Jig133.CayleyRootPotential

open CayleyRootMeasure

theorem measurable_log_norm (w : ℂ) :
    Measurable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) :=
  Real.measurable_log.comp (continuous_const.sub Complex.continuous_ofReal).norm.measurable

/-- Genuine integrability holds even if the fixed point lies on the circle. -/
theorem integrable_angular_log_sub (u : ℂ) :
    Integrable (fun θ : ℝ => Real.log ‖q θ - u‖) angular := by
  have hi : IntervalIntegrable (fun θ : ℝ => Real.log ‖q θ - u‖)
      volume 0 (2 * Real.pi) :=
    circleIntegrable_log_norm_sub_const (a := u) (c := 0) 1
  have hr : Integrable (fun θ : ℝ => Real.log ‖q θ - u‖)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hi
  exact hr.smul_measure (ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne')

theorem integral_angular_log_sub (u : ℂ) (hu : ‖u‖ ≤ 1) :
    (∫ θ, Real.log ‖q θ - u‖ ∂angular) = 0 := by
  rw [integral_angular_eq_circleAverage (fun z => Real.log ‖z - u‖),
    circleAverage_log_norm_sub_const_eq_posLog]
  exact (Real.posLog_eq_zero_iff _).mpr
    (by simpa only [abs_of_nonneg (norm_nonneg u)] using hu)

theorem integrable_angular_log_add_one :
    Integrable (fun θ : ℝ => Real.log ‖q θ + 1‖) angular := by
  simpa only [sub_neg_eq_add] using integrable_angular_log_sub (-1)

theorem integral_angular_log_add_one :
    (∫ θ, Real.log ‖q θ + 1‖ ∂angular) = 0 := by
  simpa only [sub_neg_eq_add] using integral_angular_log_sub (-1) (by simp)

/-- The literal angular parameter function is integrable by the proved AE
identity; no integrability hypothesis on the desired potential is used. -/
theorem integrable_angular_log_norm (a s : ℝ) (w : ℂ)
    (hs : 0 < s) (hw : 0 ≤ w.im) :
    Integrable (fun θ : ℝ => Real.log ‖w - (affineCayley a s θ : ℂ)‖) angular := by
  have hr := integrable_angular_log_sub (diskPoint a s w)
  have hc : Integrable (fun _ : ℝ => Real.log ‖upperShift a s w‖) angular :=
    integrable_const _
  exact ((hc.add hr).sub integrable_angular_log_add_one).congr
    ((ae_log_norm_cayley a s w hs hw).mono (fun _ h => h.symm))

theorem integral_angular_log_norm (a s : ℝ) (w : ℂ)
    (hs : 0 < s) (hw : 0 ≤ w.im) :
    (∫ θ, Real.log ‖w - (affineCayley a s θ : ℂ)‖ ∂angular) =
      Real.log ‖upperShift a s w‖ := by
  have hr := integrable_angular_log_sub (diskPoint a s w)
  have hc : Integrable (fun _ : ℝ => Real.log ‖upperShift a s w‖) angular :=
    integrable_const _
  calc
    _ = ∫ θ, Real.log ‖upperShift a s w‖ + Real.log ‖q θ - diskPoint a s w‖ -
        Real.log ‖q θ + 1‖ ∂angular :=
      integral_congr_ae (ae_log_norm_cayley a s w hs hw)
    _ = Real.log ‖upperShift a s w‖ := by
      have hsum : Integrable (fun θ : ℝ => Real.log ‖upperShift a s w‖ +
          Real.log ‖q θ - diskPoint a s w‖) angular := hc.add hr
      rw [integral_sub hsum integrable_angular_log_add_one, integral_add hc hr,
        integral_angular_log_sub (diskPoint a s w) (norm_diskPoint_le_one a s w hs hw),
        integral_angular_log_add_one]
      simp only [integral_const, probReal_univ, one_smul, add_zero, sub_zero]

/-- The zero-scale integrability statement includes the singular point w=a,
where the chosen real logarithm is totalized. -/
theorem integrable_log_norm_zero (a : ℝ) (w : ℂ) :
    Integrable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) (rootMeasure a 0) := by
  rw [rootMeasure_zero]
  exact integrable_dirac (by simp)

/-- Actual logarithmic integrability for every nonnegative scale and every
point in the closed upper half-plane. The real boundary is included. -/
theorem integrable_log_norm (a s : ℝ) (w : ℂ) (hs : 0 ≤ s) (hw : 0 ≤ w.im) :
    Integrable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) (rootMeasure a s) := by
  rcases hs.eq_or_lt with hs0 | hspos
  · subst s
    exact integrable_log_norm_zero a w
  · change Integrable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖)
      (Measure.map (affineCayley a s) angular)
    exact (integrable_map_measure (measurable_log_norm w).aestronglyMeasurable
      (measurable_affineCayley a s).aemeasurable).mpr
      (integrable_angular_log_norm a s w hspos hw)

/-- The genuine pushforward integral, not an assumed Poisson identity. -/
theorem integral_log_norm (a s : ℝ) (w : ℂ) (hs : 0 ≤ s) (hw : 0 ≤ w.im) :
    (∫ t, Real.log ‖w - (t : ℂ)‖ ∂rootMeasure a s) =
      Real.log ‖w - (a : ℂ) + (s : ℂ) * Complex.I‖ := by
  rcases hs.eq_or_lt with hs0 | hspos
  · subst s
    simp only [rootMeasure_zero, integral_dirac, Complex.ofReal_zero, zero_mul, add_zero]
  · calc
      _ = ∫ θ, Real.log ‖w - (affineCayley a s θ : ℂ)‖ ∂angular := by
        change (∫ t, Real.log ‖w - (t : ℂ)‖ ∂Measure.map (affineCayley a s) angular) = _
        exact integral_map (measurable_affineCayley a s).aemeasurable
          (measurable_log_norm w).aestronglyMeasurable
      _ = Real.log ‖w - (a : ℂ) + (s : ℂ) * Complex.I‖ :=
        integral_angular_log_norm a s w hspos hw

theorem integral_real_boundary (a s x : ℝ) (hs : 0 ≤ s) :
    (∫ t, Real.log ‖(x : ℂ) - (t : ℂ)‖ ∂rootMeasure a s) =
      Real.log ‖((x - a : ℝ) : ℂ) + (s : ℂ) * Complex.I‖ := by
  simpa only [Complex.ofReal_sub] using
    integral_log_norm a s (x : ℂ) hs (by simp)

end Jig133.CayleyRootPotential

end
end File_CayleyRootPotential

section File_InterlacingRoots

/-!
# Extracting the fresh interlacing factor

There are `m + 1` strictly increasing fresh nodes and `m` open gaps.
Opposite signs of a real polynomial at adjacent fresh nodes provide one
root in every gap. Their nodal product is monic, has degree exactly `m`,
and divides the polynomial. The quotient therefore has degree at most
`u` when the original polynomial has degree at most `m + u`.

All statements include `m = 0`: the root family is empty, its nodal
product is `1`, and the quotient is the original polynomial. No positivity
of partial-fraction residues or old-node cancellation is asserted here.
-/

open Polynomial
open scoped BigOperators

namespace Jig133.InterlacingRoots

noncomputable section

variable {m u : ℕ} {nodes : Fin (m + 1) → ℝ} {z : Fin m → ℝ}
variable {p : ℝ[X]}

/-- Strict separation of the fresh-node gaps orders any chosen points in
those gaps, independently of their being polynomial roots. -/
theorem strictMono_of_mem_gaps (hnodes : StrictMono nodes)
    (hgaps : ∀ i : Fin m, nodes i.castSucc < z i ∧ z i < nodes i.succ) :
    StrictMono z := by
  intro i j hij
  have hmiddle : nodes i.succ ≤ nodes j.castSucc :=
    hnodes.monotone (Fin.succ_le_castSucc_iff.mpr hij)
  exact lt_trans (lt_of_lt_of_le (hgaps i).2 hmiddle) (hgaps j).1

theorem injective_of_mem_gaps (hnodes : StrictMono nodes)
    (hgaps : ∀ i : Fin m, nodes i.castSucc < z i ∧ z i < nodes i.succ) :
    Function.Injective z :=
  (strictMono_of_mem_gaps hnodes hgaps).injective

/-- The intermediate value theorem selects one actual zero in each open
fresh-node gap. The assertion remains valid for the empty gap family. -/
theorem exists_interlacing_roots (hnodes : StrictMono nodes)
    (hsign : ∀ i : Fin m,
      p.eval (nodes i.castSucc) * p.eval (nodes i.succ) < 0) :
    ∃ z : Fin m → ℝ,
      (∀ i, nodes i.castSucc < z i ∧ z i < nodes i.succ) ∧
      (∀ i, p.eval (z i) = 0) ∧ StrictMono z := by
  have hroot : ∀ i : Fin m, ∃ x : ℝ,
      (nodes i.castSucc < x ∧ x < nodes i.succ) ∧ p.eval x = 0 := by
    intro i
    have hle : nodes i.castSucc ≤ nodes i.succ :=
      (hnodes i.castSucc_lt_succ).le
    rcases mul_neg_iff.mp (hsign i) with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact intermediate_value_Ioo' hle p.continuousOn ⟨hr, hl⟩
    · exact intermediate_value_Ioo hle p.continuousOn ⟨hl, hr⟩
  let z : Fin m → ℝ := fun i => Classical.choose (hroot i)
  have hgaps : ∀ i, nodes i.castSucc < z i ∧ z i < nodes i.succ :=
    fun i => (Classical.choose_spec (hroot i)).1
  have hzero : ∀ i, p.eval (z i) = 0 :=
    fun i => (Classical.choose_spec (hroot i)).2
  exact ⟨z, hgaps, hzero, strictMono_of_mem_gaps hnodes hgaps⟩

/-- Distinct actual roots give a divisor without assuming that all roots
of the polynomial are real or that these roots are simple. -/
theorem nodal_dvd_of_injective_roots (hz : Function.Injective z)
    (hzero : ∀ i, p.eval (z i) = 0) :
    Lagrange.nodal Finset.univ z ∣ p := by
  simpa only [Lagrange.nodal] using
    (Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C hz)
      (fun i => Polynomial.dvd_iff_isRoot.mpr (hzero i)))

/-- Degree accounting for the actual quotient after extracting `m`
distinct roots. The explicit nonzero premise also covers `m = 0`. -/
theorem exists_quotient_of_injective_roots (hp : p ≠ 0)
    (hz : Function.Injective z) (hzero : ∀ i, p.eval (z i) = 0)
    (hdegree : p.natDegree ≤ m + u) :
    ∃ Q : ℝ[X], Q ≠ 0 ∧ p = Lagrange.nodal Finset.univ z * Q ∧
      Q.natDegree ≤ u := by
  obtain ⟨Q, hfactor⟩ := nodal_dvd_of_injective_roots hz hzero
  have hQ : Q ≠ 0 := by
    intro hQzero
    apply hp
    simpa only [hQzero, mul_zero] using hfactor
  have hZdegree : (Lagrange.nodal Finset.univ z).natDegree = m := by
    simp only [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
  have hdegp : p.natDegree = m + Q.natDegree := by
    rw [hfactor, Polynomial.natDegree_mul Lagrange.nodal_ne_zero hQ, hZdegree]
  have hQdegree : Q.natDegree ≤ u :=
    (add_le_add_iff_left m).mp (hdegp ▸ hdegree)
  exact ⟨Q, hQ, hfactor, hQdegree⟩

/-- A complete finite extraction interface: adjacent opposite signs at all
fresh nodes produce a strictly ordered interlacing monic factor and a
nonzero quotient with the exact surplus-degree bound. -/
theorem exists_interlacing_factorization (hp : p ≠ 0)
    (hnodes : StrictMono nodes)
    (hsign : ∀ i : Fin m,
      p.eval (nodes i.castSucc) * p.eval (nodes i.succ) < 0)
    (hdegree : p.natDegree ≤ m + u) :
    ∃ (z : Fin m → ℝ) (Q : ℝ[X]),
      (∀ i, nodes i.castSucc < z i ∧ z i < nodes i.succ) ∧
      (∀ i, p.eval (z i) = 0) ∧ StrictMono z ∧
      (Lagrange.nodal Finset.univ z).Monic ∧
      (Lagrange.nodal Finset.univ z).natDegree = m ∧
      Q ≠ 0 ∧ p = Lagrange.nodal Finset.univ z * Q ∧ Q.natDegree ≤ u := by
  obtain ⟨z, hgaps, hzero, hz⟩ := exists_interlacing_roots hnodes hsign
  obtain ⟨Q, hQ, hfactor, hQdegree⟩ :=
    exists_quotient_of_injective_roots hp hz.injective hzero hdegree
  refine ⟨z, Q, hgaps, hzero, hz, Lagrange.nodal_monic, ?_,
    hQ, hfactor, hQdegree⟩
  simp only [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]

end

end Jig133.InterlacingRoots

end File_InterlacingRoots

section File_InterlacingSign

/-!
# Positive residue signs from strict interlacing

There is one root strictly between each two consecutive nodes. Pairing the
root indexed by `j` with the node indexed by `i.succAbove j` proves that the
root product and the derivative of the node product have the same nonzero
sign at node `i`. The products also cover `m = 0`.

Root extraction, divisibility of an interpolant, and analytic Cauchy-tail
bounds are separate results. This module supplies the finite sign condition
used by `PositiveCauchyFactorization` without assuming it as a premise.
-/

open Polynomial
open scoped BigOperators

namespace Jig133.InterlacingSign

noncomputable section

variable {m : ℕ}

/-- Split off any one node, indexing all the other nodes by `succAbove`. -/
theorem nodal_eq_mul_succAbove (nodes : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) :
    Lagrange.nodal Finset.univ nodes =
      (X - C (nodes i)) *
        Lagrange.nodal Finset.univ (fun j : Fin m => nodes (i.succAbove j)) := by
  change (∏ j : Fin (m + 1), (X - C (nodes j))) =
    (X - C (nodes i)) * ∏ j : Fin m, (X - C (nodes (i.succAbove j)))
  exact Fin.prod_univ_succAbove _ i

/-- At the removed node, the derivative is the product of the other factors. -/
theorem eval_derivative_nodal_eq_prod_succAbove (nodes : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) :
    (Lagrange.nodal Finset.univ nodes).derivative.eval (nodes i) =
      ∏ j : Fin m, (nodes i - nodes (i.succAbove j)) := by
  rw [nodal_eq_mul_succAbove nodes i, Polynomial.derivative_mul]
  simp [Lagrange.eval_nodal]

variable {nodes : Fin (m + 1) → ℝ} {z : Fin m → ℝ}

/-- Each paired difference product is strictly positive. -/
theorem paired_difference_pos (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ)
    (i : Fin (m + 1)) (j : Fin m) :
    0 < (nodes i - z j) * (nodes i - nodes (i.succAbove j)) := by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    have hsucc : j.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp hji
    have hz : z j < nodes i := (hgap j).2.trans_le (hnodes.monotone hsucc)
    exact mul_pos (sub_pos.mpr hz) (sub_pos.mpr (hnodes hji))
  · have hij : i ≤ j.castSucc := le_of_not_gt hji
    rw [Fin.succAbove_of_le_castSucc i j hij]
    have hz : nodes i < z j := (hnodes.monotone hij).trans_lt (hgap j).1
    have hnode : nodes i < nodes j.succ :=
      hnodes (hij.trans_lt j.castSucc_lt_succ)
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hz) (sub_neg.mpr hnode)

/-- Strict interlacing proves the nodal sign premise for positive Cauchy residues. -/
theorem interlacing_eval_mul_derivative_pos (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ)
    (i : Fin (m + 1)) :
    0 < (Lagrange.nodal Finset.univ z).eval (nodes i) *
      (Lagrange.nodal Finset.univ nodes).derivative.eval (nodes i) := by
  rw [Lagrange.eval_nodal, eval_derivative_nodal_eq_prod_succAbove nodes i]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_pos (fun j _ => paired_difference_pos hnodes hgap i j)

/-- The associated quotient by the nodal derivative is also strictly positive. -/
theorem interlacing_eval_div_derivative_pos (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ)
    (i : Fin (m + 1)) :
    0 < (Lagrange.nodal Finset.univ z).eval (nodes i) /
      (Lagrange.nodal Finset.univ nodes).derivative.eval (nodes i) := by
  exact div_pos_iff.mpr
    (mul_pos_iff.mp (interlacing_eval_mul_derivative_pos hnodes hgap i))

/-- The product over the interlacing roots is monic, including the empty product. -/
theorem interlacing_nodal_monic (z : Fin m → ℝ) :
    (Lagrange.nodal Finset.univ z).Monic :=
  Lagrange.nodal_monic

/-- There are exactly `m` linear factors in the root product. -/
theorem interlacing_nodal_natDegree (z : Fin m → ℝ) :
    (Lagrange.nodal Finset.univ z).natDegree = m := by
  simp

/-- The complete finite numerator interface needed after interlacing root extraction. -/
theorem interlacing_nodal_spec (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ) :
    (Lagrange.nodal Finset.univ z).Monic ∧
      (Lagrange.nodal Finset.univ z).natDegree = m ∧
      ∀ i : Fin (m + 1),
        0 < (Lagrange.nodal Finset.univ z).eval (nodes i) *
          (Lagrange.nodal Finset.univ nodes).derivative.eval (nodes i) := by
  exact ⟨interlacing_nodal_monic z, interlacing_nodal_natDegree z,
    interlacing_eval_mul_derivative_pos hnodes hgap⟩

end

end Jig133.InterlacingSign

end File_InterlacingSign

section File_CauchyLevelPolynomial

open Filter Polynomial
open scoped BigOperators Topology

namespace Jig133.CauchyLevelPolynomial

noncomputable section

variable {m : ℕ} {nodes : Fin (m + 1) → ℝ} {z : Fin m → ℝ}

/-- The interlacing numerator changes sign at each consecutive pair of poles. -/
theorem numerator_adjacent_product_neg (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ)
    (i : Fin m) :
    (Lagrange.nodal Finset.univ z).eval (nodes i.castSucc) *
      (Lagrange.nodal Finset.univ z).eval (nodes i.succ) < 0 := by
  classical
  rw [Lagrange.eval_nodal, Lagrange.eval_nodal, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => (nodes i.castSucc - z j) * (nodes i.succ - z j)) (Finset.mem_univ i)]
  apply mul_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr (hgap i).1) (sub_pos.mpr (hgap i).2)
  · apply Finset.prod_pos
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hzleft : z j < nodes i.castSucc :=
        (hgap j).2.trans_le (hnodes.monotone (Fin.succ_le_castSucc_iff.mpr hlt))
      have hzright : z j < nodes i.succ :=
        hzleft.trans (hnodes i.castSucc_lt_succ)
      exact mul_pos (sub_pos.mpr hzleft) (sub_pos.mpr hzright)
    · have hzright : nodes i.succ < z j :=
        (hnodes.monotone (Fin.succ_le_castSucc_iff.mpr hgt)).trans_lt (hgap j).1
      have hzleft : nodes i.castSucc < z j :=
        (hnodes i.castSucc_lt_succ).trans hzright
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hzleft) (sub_neg.mpr hzright)

theorem numerator_last_pos (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ) :
    0 < (Lagrange.nodal Finset.univ z).eval (nodes (Fin.last m)) := by
  rw [Lagrange.eval_nodal]
  apply Finset.prod_pos
  intro j _
  exact sub_pos.mpr ((hgap j).2.trans_le (hnodes.monotone j.succ.le_last))

/-- Parameter A is the reciprocal positive Cauchy level. -/
def levelPolynomial (nodes : Fin (m + 1) → ℝ) (z : Fin m → ℝ) (A : ℝ) : ℝ[X] :=
  Lagrange.nodal Finset.univ nodes - C A * Lagrange.nodal Finset.univ z

theorem levelPolynomial_monic_degree (nodes : Fin (m + 1) → ℝ)
    (z : Fin m → ℝ) (A : ℝ) :
    (levelPolynomial nodes z A).Monic ∧
      (levelPolynomial nodes z A).natDegree = m + 1 := by
  have hlow : (C A * Lagrange.nodal Finset.univ z).natDegree <
      (Lagrange.nodal Finset.univ nodes).natDegree := by
    have hh := Polynomial.natDegree_mul_le
      (p := C A) (q := Lagrange.nodal Finset.univ z)
    simp only [natDegree_C, Lagrange.natDegree_nodal, Finset.card_univ,
      Fintype.card_fin, zero_add] at hh ⊢
    exact hh.trans_lt (Nat.lt_succ_self m)
  constructor
  · change (levelPolynomial nodes z A).leadingCoeff = 1
    rw [levelPolynomial, leadingCoeff_sub_of_degree_lt (degree_lt_degree hlow)]
    exact Lagrange.nodal_monic
  · rw [levelPolynomial, natDegree_sub_eq_left_of_natDegree_lt hlow]
    simp

theorem nodal_nextCoeff {k : ℕ} (t : Fin k → ℝ) :
    (Lagrange.nodal Finset.univ t).nextCoeff = - ∑ i, t i := by
  rw [Lagrange.nodal, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_sub_C (t i))]
  simp

/-- Comparing the actual next coefficients gives the Vieta displacement A. -/
theorem sum_level_roots (A : ℝ) (u : Fin (m + 1) → ℝ)
    (heq : levelPolynomial nodes z A = Lagrange.nodal Finset.univ u) :
    (∑ i, u i) = (∑ i, nodes i) + A := by
  have hW : (Lagrange.nodal Finset.univ nodes).coeff m = - ∑ i, nodes i := by
    simpa [Polynomial.nextCoeff] using nodal_nextCoeff nodes
  have hU : (Lagrange.nodal Finset.univ u).coeff m = - ∑ i, u i := by
    simpa [Polynomial.nextCoeff] using nodal_nextCoeff u
  have hZ : (Lagrange.nodal Finset.univ z).coeff m = 1 := by
    simpa only [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] using
      (Lagrange.nodal_monic (s := Finset.univ) (v := z)).coeff_natDegree
  have hc := congrArg (fun p : ℝ[X] => p.coeff m) heq
  simp only [levelPolynomial, coeff_sub, coeff_C_mul, hW, hU, hZ, mul_one] at hc
  linarith

/-- Every positive level has one actual root to the right of every pole,
before the next pole when it exists. Their sum is fixed exactly by Vieta.
The exterior root is constructed, not assumed as an input. -/
theorem exists_positive_level_roots (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ)
    (A : ℝ) (hA : 0 < A) :
    ∃ u : Fin (m + 1) → ℝ, StrictMono u ∧
      (∀ i, nodes i < u i) ∧
      (∀ i : Fin m, u i.castSucc < nodes i.succ) ∧
      levelPolynomial nodes z A = Lagrange.nodal Finset.univ u ∧
      (∑ i, u i) = (∑ i, nodes i) + A ∧
      (∀ i, (Lagrange.nodal Finset.univ z).eval (u i) /
        (Lagrange.nodal Finset.univ nodes).eval (u i) = 1 / A) := by
  let p := levelPolynomial nodes z A
  obtain ⟨hmonic, hdegree⟩ := levelPolynomial_monic_degree nodes z A
  have hpole : ∀ i, p.eval (nodes i) = - A * (Lagrange.nodal Finset.univ z).eval (nodes i) := by
    intro i
    simp [p, levelPolynomial, Lagrange.eval_nodal_at_node (Finset.mem_univ i)]
  have hlast : p.eval (nodes (Fin.last m)) < 0 := by
    rw [hpole]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hA) (numerator_last_pos hnodes hgap)
  have hposdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by
    change 0 < (levelPolynomial nodes z A).natDegree
    rw [hdegree]
    exact Nat.succ_pos m)
  have htend : Tendsto (fun x => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hposdeg (by
      change 0 ≤ (levelPolynomial nodes z A).leadingCoeff
      rw [hmonic]
      exact zero_le_one)
  obtain ⟨R, hR, hpR⟩ := ((eventually_gt_atTop (nodes (Fin.last m))).and
    (htend.eventually (eventually_gt_atTop 0))).exists
  let extended : Fin (m + 2) → ℝ := Fin.snoc nodes R
  have hext : StrictMono extended := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    cases i using Fin.lastCases with
    | last =>
      simpa only [extended, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using hR
    | cast i =>
      simpa only [extended, Fin.succ_castSucc, Fin.snoc_castSucc] using
        hnodes i.castSucc_lt_succ
  have hsign : ∀ i : Fin (m + 1),
      p.eval (extended i.castSucc) * p.eval (extended i.succ) < 0 := by
    intro i
    cases i using Fin.lastCases with
    | last =>
      simpa only [extended, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using
        mul_neg_of_neg_of_pos hlast hpR
    | cast i =>
      have hneg := numerator_adjacent_product_neg hnodes hgap i
      have hh : p.eval (nodes i.castSucc) * p.eval (nodes i.succ) =
          A ^ 2 * ((Lagrange.nodal Finset.univ z).eval (nodes i.castSucc) *
            (Lagrange.nodal Finset.univ z).eval (nodes i.succ)) := by
        rw [hpole, hpole]
        ring
      simpa only [extended, Fin.succ_castSucc, Fin.snoc_castSucc, hh] using
        mul_neg_of_pos_of_neg (sq_pos_of_pos hA) hneg
  obtain ⟨u, hugap, huzero, humono⟩ := InterlacingRoots.exists_interlacing_roots hext hsign
  have hfactor : p = Lagrange.nodal Finset.univ u :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic hmonic
      (InterlacingRoots.nodal_dvd_of_injective_roots humono.injective huzero) (by
        simpa only [p, hdegree, Lagrange.natDegree_nodal, Finset.card_univ,
          Fintype.card_fin] using (le_rfl : m + 1 ≤ m + 1))
  refine ⟨u, humono, ?_, ?_, hfactor, sum_level_roots A u hfactor, ?_⟩
  · intro i
    simpa only [extended, Fin.snoc_castSucc] using (hugap i).1
  · intro i
    simpa only [extended, Fin.succ_castSucc, Fin.snoc_castSucc] using (hugap i.castSucc).2
  · intro i
    have havoid : ∀ j, u i ≠ nodes j := by
      intro j hEq
      have hz := huzero i
      rw [hEq, hpole] at hz
      have hZne : (Lagrange.nodal Finset.univ z).eval (nodes j) ≠ 0 :=
        (mul_pos_iff.mp (InterlacingSign.interlacing_eval_mul_derivative_pos hnodes hgap j)).elim
          (fun h => h.1.ne') (fun h => h.1.ne)
      exact (mul_ne_zero (neg_ne_zero.mpr hA.ne') hZne) hz
    have hWne := Lagrange.eval_nodal_not_at_node (fun j (_ : j ∈ Finset.univ) => havoid j)
    have hz := huzero i
    simp only [p, levelPolynomial, eval_sub, eval_mul, eval_C] at hz
    field_simp [hWne, hA.ne']
    nlinarith


end
end Jig133.CauchyLevelPolynomial
end File_CauchyLevelPolynomial

section File_FiniteCauchyAnalysis

/-!
# Basic real analysis of a finite positive Cauchy sum

The sum is finite, and every pole is excluded wherever continuity or its
derivative is asserted. Positive weights make the derivative strictly negative
on every convex region avoiding the poles. No principal-value transform of a
non-atomic measure is introduced. The probability normalization is unnecessary
for the calculus below; it is supplied separately in applications.
-/

open Filter Set
open scoped BigOperators Topology

namespace Jig133.FiniteCauchyAnalysis

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The actual finite rational Cauchy sum. Lean's total division defines it
also at poles, but the analytic statements below exclude those points. -/
def cauchy (nodes weights : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, weights i / (x - nodes i)

variable (nodes weights : ι → ℝ)

/-- The derivative of the finite sum at every point away from its poles. -/
theorem hasDerivAt_cauchy (x : ℝ) (hx : ∀ i, x ≠ nodes i) :
    HasDerivAt (cauchy nodes weights)
      (-(∑ i, weights i / (x - nodes i) ^ 2)) x := by
  have hterm : ∀ i : ι,
      HasDerivAt (fun y : ℝ => weights i / (y - nodes i))
        (-(weights i / (x - nodes i) ^ 2)) x := by
    intro i
    simpa only [id_eq, zero_mul, one_mul, mul_one, zero_sub, neg_div] using
      (hasDerivAt_const x (weights i)).fun_div
        ((hasDerivAt_id x).sub_const (nodes i)) (sub_ne_zero.mpr (hx i))
  change HasDerivAt (fun y => ∑ i, weights i / (y - nodes i))
    (-(∑ i, weights i / (x - nodes i) ^ 2)) x
  simpa only [Finset.sum_neg_distrib] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i))

theorem differentiableAt_cauchy (x : ℝ) (hx : ∀ i, x ≠ nodes i) :
    DifferentiableAt ℝ (cauchy nodes weights) x :=
  (hasDerivAt_cauchy nodes weights x hx).differentiableAt

theorem continuousAt_cauchy (x : ℝ) (hx : ∀ i, x ≠ nodes i) :
    ContinuousAt (cauchy nodes weights) x :=
  (hasDerivAt_cauchy nodes weights x hx).continuousAt

theorem deriv_cauchy (x : ℝ) (hx : ∀ i, x ≠ nodes i) :
    deriv (cauchy nodes weights) x = -(∑ i, weights i / (x - nodes i) ^ 2) :=
  (hasDerivAt_cauchy nodes weights x hx).deriv

theorem continuousOn_cauchy {D : Set ℝ} (hD : ∀ x ∈ D, ∀ i, x ≠ nodes i) :
    ContinuousOn (cauchy nodes weights) D :=
  fun x hx => (continuousAt_cauchy nodes weights x (hD x hx)).continuousWithinAt

/-- With a nonempty positive support the derivative is strictly negative. -/
theorem deriv_cauchy_neg [Nonempty ι] (hw : ∀ i, 0 < weights i)
    (x : ℝ) (hx : ∀ i, x ≠ nodes i) :
    deriv (cauchy nodes weights) x < 0 := by
  rw [deriv_cauchy nodes weights x hx]
  apply neg_neg_of_pos
  exact Finset.sum_pos
    (fun i _ => div_pos (hw i) (sq_pos_of_ne_zero (sub_ne_zero.mpr (hx i))))
    Finset.univ_nonempty

/-- Every convex region avoiding the poles carries a strictly decreasing
Cauchy sum. This covers open gaps and either unbounded exterior interval. -/
theorem strictAntiOn_cauchy [Nonempty ι] (hw : ∀ i, 0 < weights i)
    {D : Set ℝ} (hconvex : Convex ℝ D)
    (hD : ∀ x ∈ D, ∀ i, x ≠ nodes i) :
    StrictAntiOn (cauchy nodes weights) D := by
  apply strictAntiOn_of_deriv_neg hconvex (continuousOn_cauchy nodes weights hD)
  intro x hx
  exact deriv_cauchy_neg nodes weights hw x (hD x (interior_subset hx))

/-- Right of all nodes every term has positive sign. -/
theorem cauchy_pos_of_nodes_lt [Nonempty ι] (hw : ∀ i, 0 < weights i)
    {x : ℝ} (hx : ∀ i, nodes i < x) : 0 < cauchy nodes weights x := by
  exact Finset.sum_pos (fun i _ => div_pos (hw i) (sub_pos.mpr (hx i)))
    Finset.univ_nonempty

/-- Left of all nodes every term has negative sign. -/
theorem cauchy_neg_of_lt_nodes [Nonempty ι] (hw : ∀ i, 0 < weights i)
    {x : ℝ} (hx : ∀ i, x < nodes i) : cauchy nodes weights x < 0 := by
  have hpos : 0 < ∑ i, -(weights i / (x - nodes i)) :=
    Finset.sum_pos
      (fun i _ => neg_pos.mpr (div_neg_of_pos_of_neg (hw i) (sub_neg.mpr (hx i))))
      Finset.univ_nonempty
  simpa only [Finset.sum_neg_distrib, neg_pos, cauchy] using hpos

/-- Every finite Cauchy sum tends to zero at positive infinity. -/
theorem tendsto_cauchy_atTop : Tendsto (cauchy nodes weights) atTop (𝓝 0) := by
  have hterm : ∀ i : ι,
      Tendsto (fun x : ℝ => weights i / (x - nodes i)) atTop (𝓝 0) := by
    intro i
    have hlin : Tendsto (fun x : ℝ => x - nodes i) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (b + nodes i)] with x hx
      linarith
    exact hlin.const_div_atTop (weights i)
  change Tendsto (fun x => ∑ i, weights i / (x - nodes i)) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun i _ => hterm i))

/-- Every finite Cauchy sum tends to zero at negative infinity. -/
theorem tendsto_cauchy_atBot : Tendsto (cauchy nodes weights) atBot (𝓝 0) := by
  have hterm : ∀ i : ι,
      Tendsto (fun x : ℝ => weights i / (x - nodes i)) atBot (𝓝 0) := by
    intro i
    have hlin : Tendsto (fun x : ℝ => x - nodes i) atBot atBot := by
      apply tendsto_atBot.mpr
      intro b
      filter_upwards [eventually_le_atBot (b + nodes i)] with x hx
      linarith
    exact hlin.const_div_atBot (weights i)
  change Tendsto (fun x => ∑ i, weights i / (x - nodes i)) atBot (𝓝 0)
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun i _ => hterm i))

/-- Approaching any distinct pole from the right sends the positive Cauchy
sum to positive infinity. The other finitely many terms have finite limits. -/
theorem tendsto_cauchy_nhdsGT_pole (hnodes : Function.Injective nodes)
    (hw : ∀ i, 0 < weights i) (i : ι) :
    Tendsto (cauchy nodes weights) (𝓝[>] (nodes i)) atTop := by
  classical
  let R := ∑ j ∈ Finset.univ.erase i, weights j / (nodes i - nodes j)
  have hrest : Tendsto
      (fun x : ℝ => ∑ j ∈ Finset.univ.erase i, weights j / (x - nodes j))
      (𝓝 (nodes i)) (𝓝 R) := by
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_const_nhds.div (tendsto_id.sub_const (nodes j))
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hj).1 (hnodes heq.symm)
  have hsub : Tendsto (fun x : ℝ => x - nodes i)
      (𝓝[>] (nodes i)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun x : ℝ => x - nodes i) (𝓝 (nodes i)) (𝓝 0) := by
        simpa only [id_eq, sub_self] using
          (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 (nodes i)) (𝓝 (nodes i))).sub_const
            (nodes i)
      exact hc.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (show nodes i < x from hx)
  have hpole : Tendsto (fun x : ℝ => weights i / (x - nodes i))
      (𝓝[>] (nodes i)) atTop := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      (tendsto_inv_nhdsGT_zero.comp hsub).const_mul_atTop (hw i)
  have hsplit (x : ℝ) : cauchy nodes weights x = weights i / (x - nodes i) +
      ∑ j ∈ Finset.univ.erase i, weights j / (x - nodes j) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
  apply tendsto_atTop.mpr
  intro b
  have hlarge := (tendsto_atTop.mp hpole) (b - R + 1)
  have hnear := (hrest.mono_left (show (𝓝[>] (nodes i)) ≤ 𝓝 (nodes i) from inf_le_left)).eventually_const_le
    (show R - 1 < R by linarith)
  filter_upwards [hlarge, hnear] with x hx hy
  rw [hsplit]
  linarith

/-- Approaching a distinct pole from the left sends the sum to negative
infinity, with the same finite regular remainder. -/
theorem tendsto_cauchy_nhdsLT_pole (hnodes : Function.Injective nodes)
    (hw : ∀ i, 0 < weights i) (i : ι) :
    Tendsto (cauchy nodes weights) (𝓝[<] (nodes i)) atBot := by
  classical
  let R := ∑ j ∈ Finset.univ.erase i, weights j / (nodes i - nodes j)
  have hrest : Tendsto
      (fun x : ℝ => ∑ j ∈ Finset.univ.erase i, weights j / (x - nodes j))
      (𝓝 (nodes i)) (𝓝 R) := by
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_const_nhds.div (tendsto_id.sub_const (nodes j))
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hj).1 (hnodes heq.symm)
  have hsub : Tendsto (fun x : ℝ => x - nodes i)
      (𝓝[<] (nodes i)) (𝓝[<] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun x : ℝ => x - nodes i) (𝓝 (nodes i)) (𝓝 0) := by
        simpa only [id_eq, sub_self] using
          (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 (nodes i)) (𝓝 (nodes i))).sub_const
            (nodes i)
      exact hc.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_neg.mpr (show x < nodes i from hx)
  have hpole : Tendsto (fun x : ℝ => weights i / (x - nodes i))
      (𝓝[<] (nodes i)) atBot := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      (tendsto_inv_nhdsLT_zero.comp hsub).const_mul_atBot (hw i)
  have hsplit (x : ℝ) : cauchy nodes weights x = weights i / (x - nodes i) +
      ∑ j ∈ Finset.univ.erase i, weights j / (x - nodes j) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
  apply tendsto_atBot.mpr
  intro b
  have hlarge := (tendsto_atBot.mp hpole) (b - R - 1)
  have hnear := (hrest.mono_left (show (𝓝[<] (nodes i)) ≤ 𝓝 (nodes i) from inf_le_left)).eventually_le_const
    (show R < R + 1 by linarith)
  filter_upwards [hlarge, hnear] with x hx hy
  rw [hsplit]
  linarith

end

noncomputable section OrderedNodes

variable {m : ℕ} (nodes weights : Fin (m + 1) → ℝ)

/-- An actual open gap contains none of the strictly ordered nodes. -/
theorem gap_avoids_nodes (hnodes : StrictMono nodes) (i : Fin m)
    {x : ℝ} (hx : x ∈ Ioo (nodes i.castSucc) (nodes i.succ)) :
    ∀ j, x ≠ nodes j := by
  intro j
  by_cases hj : j ≤ i.castSucc
  · exact ne_of_gt ((hnodes.monotone hj).trans_lt hx.1)
  · have hij : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hj)
    exact ne_of_lt (hx.2.trans_le (hnodes.monotone hij))

theorem continuousOn_gap (hnodes : StrictMono nodes) (i : Fin m) :
    ContinuousOn (cauchy nodes weights) (Ioo (nodes i.castSucc) (nodes i.succ)) :=
  continuousOn_cauchy nodes weights (fun _ hx => gap_avoids_nodes nodes hnodes i hx)

theorem strictAntiOn_gap (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i)
    (i : Fin m) :
    StrictAntiOn (cauchy nodes weights) (Ioo (nodes i.castSucc) (nodes i.succ)) :=
  strictAntiOn_cauchy nodes weights hw (convex_Ioo _ _)
    (fun _ hx => gap_avoids_nodes nodes hnodes i hx)

theorem cauchy_pos_right (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i)
    {x : ℝ} (hx : nodes (Fin.last m) < x) : 0 < cauchy nodes weights x :=
  cauchy_pos_of_nodes_lt nodes weights hw
    (fun i => (hnodes.monotone i.le_last).trans_lt hx)

theorem cauchy_neg_left (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i)
    {x : ℝ} (hx : x < nodes 0) : cauchy nodes weights x < 0 :=
  cauchy_neg_of_lt_nodes nodes weights hw
    (fun i => hx.trans_le (hnodes.monotone (Fin.zero_le i)))

theorem strictAntiOn_right (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i) :
    StrictAntiOn (cauchy nodes weights) (Ioi (nodes (Fin.last m))) := by
  apply strictAntiOn_cauchy nodes weights hw (convex_Ioi _)
  intro x hx i
  exact ne_of_gt ((hnodes.monotone i.le_last).trans_lt hx)

theorem strictAntiOn_left (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i) :
    StrictAntiOn (cauchy nodes weights) (Iio (nodes 0)) := by
  apply strictAntiOn_cauchy nodes weights hw (convex_Iio _)
  intro x hx i
  exact ne_of_lt (hx.trans_le (hnodes.monotone (Fin.zero_le i)))

/-- Every real level occurs exactly once in each actual internal gap. -/
theorem existsUnique_level_gap (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i)
    (i : Fin m) (y : ℝ) :
    ∃! x : ℝ, x ∈ Ioo (nodes i.castSucc) (nodes i.succ) ∧
      cauchy nodes weights x = y := by
  have hab : nodes i.castSucc < nodes i.succ := hnodes i.castSucc_lt_succ
  have hleft : (𝓝[>] (nodes i.castSucc)) ≤
      𝓟 (Ioo (nodes i.castSucc) (nodes i.succ)) :=
    le_principal_iff.mpr (Ioo_mem_nhdsGT hab)
  have hright : (𝓝[<] (nodes i.succ)) ≤
      𝓟 (Ioo (nodes i.castSucc) (nodes i.succ)) :=
    le_principal_iff.mpr (Ioo_mem_nhdsLT hab)
  obtain ⟨x, hx, hxy⟩ := isPreconnected_Ioo.intermediate_value₂_eventually₂
    hright hleft (continuousOn_gap nodes weights hnodes i) continuousOn_const
    ((tendsto_atBot.mp
      (tendsto_cauchy_nhdsLT_pole nodes weights hnodes.injective hw i.succ)) y)
    ((tendsto_atTop.mp
      (tendsto_cauchy_nhdsGT_pole nodes weights hnodes.injective hw i.castSucc)) y)
  refine ⟨x, ⟨hx, hxy⟩, ?_⟩
  intro z hz
  exact StrictAntiOn.injOn (strictAntiOn_gap nodes weights hnodes hw i) hz.1 hx
    (hz.2.trans hxy.symm)

/-- Every positive level occurs exactly once to the right of the last node. -/
theorem existsUnique_positive_level_right (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) (y : ℝ) (hy : 0 < y) :
    ∃! x : ℝ, nodes (Fin.last m) < x ∧ cauchy nodes weights x = y := by
  have htop : (atTop : Filter ℝ) ≤ 𝓟 (Ioi (nodes (Fin.last m))) :=
    le_principal_iff.mpr (eventually_gt_atTop _)
  have hright : (𝓝[>] (nodes (Fin.last m))) ≤ 𝓟 (Ioi (nodes (Fin.last m))) :=
    inf_le_right
  have hcont : ContinuousOn (cauchy nodes weights) (Ioi (nodes (Fin.last m))) :=
    continuousOn_cauchy nodes weights (fun x hx i =>
      ne_of_gt ((hnodes.monotone i.le_last).trans_lt hx))
  obtain ⟨x, hx, hxy⟩ := isPreconnected_Ioi.intermediate_value₂_eventually₂
    htop hright hcont continuousOn_const
    ((tendsto_cauchy_atTop nodes weights).eventually_le_const hy)
    ((tendsto_atTop.mp
      (tendsto_cauchy_nhdsGT_pole nodes weights hnodes.injective hw (Fin.last m))) y)
  refine ⟨x, ⟨hx, hxy⟩, ?_⟩
  intro z hz
  exact StrictAntiOn.injOn (strictAntiOn_right nodes weights hnodes hw) hz.1 hx
    (hz.2.trans hxy.symm)

/-- Every negative level occurs exactly once to the left of the first node. -/
theorem existsUnique_negative_level_left (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) (y : ℝ) (hy : y < 0) :
    ∃! x : ℝ, x < nodes 0 ∧ cauchy nodes weights x = y := by
  have hbot : (atBot : Filter ℝ) ≤ 𝓟 (Iio (nodes 0)) :=
    le_principal_iff.mpr (eventually_lt_atBot _)
  have hleft : (𝓝[<] (nodes 0)) ≤ 𝓟 (Iio (nodes 0)) := inf_le_right
  have hcont : ContinuousOn (cauchy nodes weights) (Iio (nodes 0)) :=
    continuousOn_cauchy nodes weights (fun x hx i =>
      ne_of_lt (hx.trans_le (hnodes.monotone (Fin.zero_le i))))
  obtain ⟨x, hx, hxy⟩ := isPreconnected_Iio.intermediate_value₂_eventually₂
    hleft hbot hcont continuousOn_const
    ((tendsto_atBot.mp
      (tendsto_cauchy_nhdsLT_pole nodes weights hnodes.injective hw 0)) y)
    ((tendsto_cauchy_atBot nodes weights).eventually_const_le hy)
  refine ⟨x, ⟨hx, hxy⟩, ?_⟩
  intro z hz
  exact StrictAntiOn.injOn (strictAntiOn_left nodes weights hnodes hw) hz.1 hx
    (hz.2.trans hxy.symm)

end OrderedNodes


end Jig133.FiniteCauchyAnalysis
end File_FiniteCauchyAnalysis

section File_FiniteCauchyLevels

open Polynomial
open scoped BigOperators

namespace Jig133.FiniteCauchyLevels

noncomputable section

open CauchyLevelPolynomial FiniteCauchyAnalysis

variable {m : ℕ} {nodes weights : Fin (m + 1) → ℝ} {z : Fin m → ℝ}

/-- Points in the right-hand gap of each pole, including its exterior gap,
avoid every original pole. -/
theorem positive_array_avoids_nodes (hnodes : StrictMono nodes)
    (u : Fin (m + 1) → ℝ) (hleft : ∀ i, nodes i < u i)
    (hright : ∀ i : Fin m, u i.castSucc < nodes i.succ) :
    ∀ i j, u i ≠ nodes j := by
  intro i
  cases i using Fin.lastCases with
  | last =>
    intro j
    exact ne_of_gt ((hnodes.monotone j.le_last).trans_lt (hleft (Fin.last m)))
  | cast i =>
    exact gap_avoids_nodes nodes hnodes i ⟨hleft i.castSucc, hright i⟩

/-- Points in the left-hand gap of each pole, including its exterior gap,
avoid every original pole. -/
theorem negative_array_avoids_nodes (hnodes : StrictMono nodes)
    (v : Fin (m + 1) → ℝ) (hright : ∀ i, v i < nodes i)
    (hleft : ∀ i : Fin m, nodes i.castSucc < v i.succ) :
    ∀ i j, v i ≠ nodes j := by
  intro i
  cases i using Fin.cases with
  | zero =>
    intro j
    exact ne_of_lt ((hright 0).trans_le (hnodes.monotone (Fin.zero_le j)))
  | succ i =>
    exact gap_avoids_nodes nodes hnodes i ⟨hleft i, hright i.succ⟩

/-- The actual negative exterior and internal levels form the complete root
array of W + A Z. The polynomial identity fixes their Vieta sum. -/
theorem exists_negative_level_roots (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i)
    (hratio : ∀ x : ℝ, (∀ j, x ≠ nodes j) →
      (Lagrange.nodal Finset.univ z).eval x /
        (Lagrange.nodal Finset.univ nodes).eval x = cauchy nodes weights x)
    (A : ℝ) (hA : 0 < A) :
    ∃ v : Fin (m + 1) → ℝ, StrictMono v ∧
      (∀ i, v i < nodes i) ∧
      (∀ i : Fin m, nodes i.castSucc < v i.succ) ∧
      (∀ i j, v i ≠ nodes j) ∧
      (∀ i, cauchy nodes weights (v i) = -(1 / A)) ∧
      levelPolynomial nodes z (-A) = Lagrange.nodal Finset.univ v ∧
      (∑ i, v i) = (∑ i, nodes i) - A := by
  have hneg : -(1 / A) < 0 := neg_neg_of_pos (one_div_pos.mpr hA)
  obtain ⟨l, hl, hllevel⟩ :=
    (existsUnique_negative_level_left nodes weights hnodes hw (-(1 / A)) hneg).exists
  have hinner : ∀ i : Fin m, ∃ x : ℝ,
      x ∈ Set.Ioo (nodes i.castSucc) (nodes i.succ) ∧
        cauchy nodes weights x = -(1 / A) := fun i =>
    (existsUnique_level_gap nodes weights hnodes hw i (-(1 / A))).exists
  choose q hq hqlevel using hinner
  let v : Fin (m + 1) → ℝ := Fin.cons l q
  have hvright : ∀ i, v i < nodes i := by
    intro i
    cases i using Fin.cases with
    | zero => simpa only [v, Fin.cons_zero] using hl
    | succ i => simpa only [v, Fin.cons_succ] using (hq i).2
  have hvleft : ∀ i : Fin m, nodes i.castSucc < v i.succ := by
    intro i
    simpa only [v, Fin.cons_succ] using (hq i).1
  have hvmono : StrictMono v := Fin.strictMono_iff_lt_succ.mpr
    (fun i => (hvright i.castSucc).trans (hvleft i))
  have hvavoid : ∀ i j, v i ≠ nodes j :=
    negative_array_avoids_nodes hnodes v hvright hvleft
  have hvlevel : ∀ i, cauchy nodes weights (v i) = -(1 / A) := by
    intro i
    cases i using Fin.cases with
    | zero => simpa only [v, Fin.cons_zero] using hllevel
    | succ i => simpa only [v, Fin.cons_succ] using hqlevel i
  have hvzero : ∀ i, (levelPolynomial nodes z (-A)).eval (v i) = 0 := by
    intro i
    have hWne := Lagrange.eval_nodal_not_at_node
      (fun j (_ : j ∈ Finset.univ) => hvavoid i j)
    have hr := hratio (v i) (hvavoid i)
    rw [hvlevel i] at hr
    field_simp [hWne, hA.ne'] at hr
    simp only [levelPolynomial, eval_sub, eval_mul, eval_C]
    nlinarith [hr]
  obtain ⟨hmonic, hdegree⟩ := levelPolynomial_monic_degree nodes z (-A)
  have hfactor : levelPolynomial nodes z (-A) = Lagrange.nodal Finset.univ v :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic hmonic
      (InterlacingRoots.nodal_dvd_of_injective_roots hvmono.injective hvzero) (by
        simpa only [hdegree, Lagrange.natDegree_nodal, Finset.card_univ,
          Fintype.card_fin] using (le_rfl : m + 1 ≤ m + 1))
  have hsum : (∑ i, v i) = (∑ i, nodes i) - A := by
    simpa only [sub_eq_add_neg] using sum_level_roots (-A) v hfactor
  exact ⟨v, hvmono, hvright, hvleft, hvavoid, hvlevel, hfactor, hsum⟩

/-- Strict decrease in an actual pole gap orders its positive and negative
levels. All endpoint and pole exclusions are explicit through gap membership. -/
theorem positive_level_lt_negative_level (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) (i : Fin m) (A : ℝ) (hA : 0 < A)
    (u v : ℝ) (hu : u ∈ Set.Ioo (nodes i.castSucc) (nodes i.succ))
    (hv : v ∈ Set.Ioo (nodes i.castSucc) (nodes i.succ))
    (hulevel : cauchy nodes weights u = 1 / A)
    (hvlevel : cauchy nodes weights v = -(1 / A)) : u < v := by
  apply ((strictAntiOn_gap nodes weights hnodes hw i).lt_iff_gt hv hu).mp
  rw [hulevel, hvlevel]
  linarith [one_div_pos.mpr hA]

theorem positive_length_sum (u : Fin (m + 1) → ℝ) (A : ℝ)
    (hsum : (∑ i, u i) = (∑ i, nodes i) + A) :
    (∑ i, (u i - nodes i)) = A := by
  rw [Finset.sum_sub_distrib, hsum]
  ring

theorem negative_length_sum (v : Fin (m + 1) → ℝ) (A : ℝ)
    (hsum : (∑ i, v i) = (∑ i, nodes i) - A) :
    (∑ i, (nodes i - v i)) = A := by
  rw [Finset.sum_sub_distrib, hsum]
  ring

/-- The two Vieta sums identify the entire internal low-level length with
the excess separation of the two exterior levels. The empty internal sum is included. -/
theorem internal_length_sum (u v : Fin (m + 1) → ℝ) (A : ℝ)
    (hu : (∑ i, u i) = (∑ i, nodes i) + A)
    (hv : (∑ i, v i) = (∑ i, nodes i) - A) :
    (∑ i : Fin m, (v i.succ - u i.castSucc)) =
      u (Fin.last m) - v 0 - 2 * A := by
  rw [Finset.sum_sub_distrib]
  have hu' := Fin.sum_univ_castSucc u
  have hv' := Fin.sum_univ_succ v
  linarith

/-- A complete finite interface for the two signed Cauchy level arrays.
Existence and ordering are proved from the actual positive atomic sum and
its monic interlacing ratio; no level endpoints or sum identities are assumed. -/
theorem exists_signed_level_arrays (hnodes : StrictMono nodes)
    (hgap : ∀ j : Fin m, nodes j.castSucc < z j ∧ z j < nodes j.succ)
    (hw : ∀ i, 0 < weights i)
    (hratio : ∀ x : ℝ, (∀ j, x ≠ nodes j) →
      (Lagrange.nodal Finset.univ z).eval x /
        (Lagrange.nodal Finset.univ nodes).eval x = cauchy nodes weights x)
    (A : ℝ) (hA : 0 < A) :
    ∃ u v : Fin (m + 1) → ℝ, StrictMono u ∧ StrictMono v ∧
      (∀ i, nodes i < u i) ∧
      (∀ i : Fin m, u i.castSucc < nodes i.succ) ∧
      (∀ i, v i < nodes i) ∧
      (∀ i : Fin m, nodes i.castSucc < v i.succ) ∧
      (∀ i j, u i ≠ nodes j) ∧ (∀ i j, v i ≠ nodes j) ∧
      (∀ i, cauchy nodes weights (u i) = 1 / A) ∧
      (∀ i, cauchy nodes weights (v i) = -(1 / A)) ∧
      levelPolynomial nodes z A = Lagrange.nodal Finset.univ u ∧
      levelPolynomial nodes z (-A) = Lagrange.nodal Finset.univ v ∧
      (∑ i, u i) = (∑ i, nodes i) + A ∧
      (∑ i, v i) = (∑ i, nodes i) - A ∧
      (∀ i : Fin m, u i.castSucc < v i.succ) ∧
      (∑ i, (u i - nodes i)) = A ∧
      (∑ i, (nodes i - v i)) = A ∧
      (∑ i : Fin m, (v i.succ - u i.castSucc)) =
        u (Fin.last m) - v 0 - 2 * A := by
  obtain ⟨u, humono, huleft, huright, hufactor, husum, huratio⟩ :=
    CauchyLevelPolynomial.exists_positive_level_roots hnodes hgap A hA
  have huavoid : ∀ i j, u i ≠ nodes j :=
    positive_array_avoids_nodes hnodes u huleft huright
  have hulevel : ∀ i, cauchy nodes weights (u i) = 1 / A :=
    fun i => (hratio (u i) (huavoid i)).symm.trans (huratio i)
  obtain ⟨v, hvmono, hvright, hvleft, hvavoid, hvlevel, hvfactor, hvsum⟩ :=
    exists_negative_level_roots hnodes hw hratio A hA
  have horder : ∀ i : Fin m, u i.castSucc < v i.succ := by
    intro i
    exact positive_level_lt_negative_level hnodes hw i A hA (u i.castSucc) (v i.succ)
      ⟨huleft i.castSucc, huright i⟩ ⟨hvleft i, hvright i.succ⟩
      (hulevel i.castSucc) (hvlevel i.succ)
  exact ⟨u, v, humono, hvmono, huleft, huright, hvright, hvleft, huavoid, hvavoid,
    hulevel, hvlevel, hufactor, hvfactor, husum, hvsum, horder,
    positive_length_sum u A husum, negative_length_sum v A hvsum,
    internal_length_sum u v A husum hvsum⟩


end
end Jig133.FiniteCauchyLevels
end File_FiniteCauchyLevels

section File_FiniteLevelGeometry

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Jig133.FiniteLevelGeometry

noncomputable section

variable {m : ℕ} (nodes : Fin (m + 1) → ℝ)

/-- Every nonpole lies in an actual gap or one of the two exterior intervals. -/
theorem location_of_not_pole {x : ℝ} (hx : ∀ i, x ≠ nodes i) :
    x < nodes 0 ∨ nodes (Fin.last m) < x ∨
      ∃ i : Fin m, x ∈ Ioo (nodes i.castSucc) (nodes i.succ) := by
  classical
  by_cases hl : x < nodes 0
  · exact Or.inl hl
  by_cases hr : nodes (Fin.last m) < x
  · exact Or.inr (Or.inl hr)
  let s := Finset.univ.filter (fun i => nodes i < x)
  have hs : s.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact lt_of_le_of_ne (le_of_not_gt hl) (hx 0).symm
  let k := s.max' hs
  have hkx : nodes k < x := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hk : k.val < m := by
    have hne : k ≠ Fin.last m := by intro h; exact hr (h ▸ hkx)
    have hle := k.le_last
    have hlt := lt_of_le_of_ne hle hne
    exact hlt
  let i : Fin m := k.castLT hk
  have hki : i.castSucc = k := Fin.castSucc_castLT k hk
  have hnext : x < nodes i.succ := by
    by_contra h
    have hless : nodes i.succ < x :=
      lt_of_le_of_ne (le_of_not_gt h) (hx i.succ).symm
    have hmem : i.succ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hless⟩
    have hle : i.succ ≤ k := s.le_max' i.succ hmem
    have hlt : k < i.succ := hki ▸ i.castSucc_lt_succ
    exact (not_le_of_gt hlt) hle
  exact Or.inr (Or.inr ⟨i, hki ▸ hkx, hnext⟩)

/-- Only monotonicity within each actual pole-free interval is requested. -/
structure DecreasingGaps (G : ℝ → ℝ) : Prop where
  left : StrictAntiOn G (Iio (nodes 0))
  right : StrictAntiOn G (Ioi (nodes (Fin.last m)))
  gap : ∀ i : Fin m, StrictAntiOn G (Ioo (nodes i.castSucc) (nodes i.succ))

variable {nodes} {G : ℝ → ℝ}

theorem positive_level_cover (hG : DecreasingGaps nodes G)
    (hleft : ∀ x, x < nodes 0 → G x < 0)
    (u : Fin (m + 1) → ℝ) (hu : ∀ i, nodes i < u i)
    (hugap : ∀ i : Fin m, u i.castSucc < nodes i.succ)
    (L : ℝ) (hL : 0 < L) (hlevel : ∀ i, G (u i) = L) :
    {x | L < G x} ⊆ range nodes ∪ ⋃ i, Ioo (nodes i) (u i) := by
  intro x hx
  change L < G x at hx
  by_cases hp : x ∈ range nodes
  · exact Or.inl hp
  have havoid : ∀ i, x ≠ nodes i := fun i h => hp ⟨i, h.symm⟩
  right
  rcases location_of_not_pole nodes havoid with hl | hr | ⟨i, hgap⟩
  · exact False.elim (by have := hleft x hl; linarith)
  · apply mem_iUnion.mpr
    refine ⟨Fin.last m, hr, ?_⟩
    rcases lt_trichotomy x (u (Fin.last m)) with h | h | h
    · exact h
    · have := hlevel (Fin.last m); rw [← h] at this; linarith
    · have := hG.right (hu (Fin.last m)) hr h
      rw [hlevel] at this
      linarith
  · apply mem_iUnion.mpr
    refine ⟨i.castSucc, hgap.1, ?_⟩
    rcases lt_trichotomy x (u i.castSucc) with h | h | h
    · exact h
    · have := hlevel i.castSucc; rw [← h] at this; linarith
    · have := hG.gap i ⟨hu i.castSucc, hugap i⟩ hgap h
      rw [hlevel] at this
      linarith

theorem negative_level_cover (hG : DecreasingGaps nodes G)
    (hright : ∀ x, nodes (Fin.last m) < x → 0 < G x)
    (v : Fin (m + 1) → ℝ) (hv : ∀ i, v i < nodes i)
    (hvgap : ∀ i : Fin m, nodes i.castSucc < v i.succ)
    (L : ℝ) (hL : 0 < L) (hlevel : ∀ i, G (v i) = -L) :
    {x | G x < -L} ⊆ range nodes ∪ ⋃ i, Ioo (v i) (nodes i) := by
  intro x hx
  change G x < -L at hx
  by_cases hp : x ∈ range nodes
  · exact Or.inl hp
  have havoid : ∀ i, x ≠ nodes i := fun i h => hp ⟨i, h.symm⟩
  right
  rcases location_of_not_pole nodes havoid with hl | hr | ⟨i, hgap⟩
  · apply mem_iUnion.mpr
    refine ⟨0, ?_, hl⟩
    rcases lt_trichotomy (v 0) x with h | h | h
    · exact h
    · have := hlevel 0; rw [h] at this; linarith
    · have := hG.left hl (hv 0) h
      rw [hlevel] at this
      linarith
  · exact False.elim (by have := hright x hr; linarith)
  · apply mem_iUnion.mpr
    refine ⟨i.succ, ?_, hgap.2⟩
    rcases lt_trichotomy (v i.succ) x with h | h | h
    · exact h
    · have := hlevel i.succ; rw [h] at this; linarith
    · have := hG.gap i hgap ⟨hvgap i, hv i.succ⟩ h
      rw [hlevel] at this
      linarith

theorem small_absolute_level_cover (hG : DecreasingGaps nodes G)
    (u v : Fin (m + 1) → ℝ)
    (hu : ∀ i, nodes i < u i) (hv : ∀ i, v i < nodes i)
    (hugap : ∀ i : Fin m, u i.castSucc < nodes i.succ)
    (hvgap : ∀ i : Fin m, nodes i.castSucc < v i.succ)
    (L : ℝ) (hulevel : ∀ i, G (u i) = L) (hvlevel : ∀ i, G (v i) = -L)
    (huI : 1 < u (Fin.last m)) (hvI : v 0 < -1) :
    {x | x ∈ Icc (-1 : ℝ) 1 ∧ |G x| ≤ L} ⊆
      range nodes ∪ ⋃ i : Fin m, Icc (u i.castSucc) (v i.succ) := by
  rintro x ⟨hxI, hx⟩
  have hb := abs_le.mp hx
  by_cases hp : x ∈ range nodes
  · exact Or.inl hp
  have havoid : ∀ i, x ≠ nodes i := fun i h => hp ⟨i, h.symm⟩
  right
  rcases location_of_not_pole nodes havoid with hl | hr | ⟨i, hgap⟩
  · have hlt : v 0 < x := hvI.trans_le hxI.1
    have hh := hG.left (hv 0) hl hlt
    rw [hvlevel] at hh
    exact False.elim (not_lt_of_ge hb.1 hh)
  · have hlt : x < u (Fin.last m) := hxI.2.trans_lt huI
    have hh := hG.right hr (hu (Fin.last m)) hlt
    rw [hulevel] at hh
    exact False.elim (not_lt_of_ge hb.2 hh)
  · apply mem_iUnion.mpr
    refine ⟨i, ?_, ?_⟩
    · by_contra h
      have hh := hG.gap i hgap ⟨hu i.castSucc, hugap i⟩ (lt_of_not_ge h)
      rw [hulevel] at hh
      exact (not_lt_of_ge hb.2) hh
    · by_contra h
      have hh := hG.gap i ⟨hvgap i, hv i.succ⟩ hgap (lt_of_not_ge h)
      rw [hvlevel] at hh
      exact (not_lt_of_ge hb.1) hh

/-- A finite null exception and an actual finite interval cover suffice for
the length estimate; no measurability of the covered set is assumed. -/
theorem volume_le_sum_lengths {κ : Type*} [Fintype κ]
    (a b : κ → ℝ) (hab : ∀ i, a i ≤ b i) (s : Set ℝ) (hs : s.Finite)
    (T : Set ℝ) (hT : T ⊆ s ∪ ⋃ i, Icc (a i) (b i)) :
    volume T ≤ ENNReal.ofReal (∑ i, (b i - a i)) := by
  calc
    volume T ≤ volume (s ∪ ⋃ i, Icc (a i) (b i)) := measure_mono hT
    _ ≤ volume s + volume (⋃ i, Icc (a i) (b i)) := measure_union_le _ _
    _ = volume (⋃ i, Icc (a i) (b i)) := by rw [hs.measure_zero volume, zero_add]
    _ ≤ ∑ i, volume (Icc (a i) (b i)) := measure_iUnion_fintype_le volume _
    _ = ENNReal.ofReal (∑ i, (b i - a i)) := by
      simp only [Real.volume_Icc]
      exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hab i))).symm


end
end Jig133.FiniteLevelGeometry
end File_FiniteLevelGeometry

section File_AtomicCauchyBoole

/-!
# Boole upper tails for an arbitrary finite positive atomic Cauchy sum

The weighted numerator and both signed level arrays are constructed from the
actual nodes and weights. No interlacing numerator, ratio identity, probability
normalization, or support interval is assumed. The finite set of totalized
poles has zero Lebesgue measure. The final statements include an empty row.
-/

open Set MeasureTheory Polynomial
open scoped BigOperators ENNReal

noncomputable section

namespace Jig133.AtomicCauchyBoole

open FiniteCauchyAnalysis FiniteLevelGeometry

/-- The actual numerator obtained by clearing all original denominators. -/
def numerator {n : ℕ} (nodes weights : Fin n → ℝ) : ℝ[X] :=
  ∑ i, C (weights i) * Lagrange.nodal (Finset.univ.erase i) nodes

/-- The monic normalization of the actual signed-level polynomial. -/
def levelPolynomial {n : ℕ} (nodes weights : Fin n → ℝ) (A : ℝ) : ℝ[X] :=
  Lagrange.nodal Finset.univ nodes - C A * numerator nodes weights

/-- At A=1/L the normalization is exactly L⁻¹ times LW-N. -/
theorem scale_levelPolynomial {n : ℕ} (nodes weights : Fin n → ℝ)
    (L : ℝ) (hL : L ≠ 0) :
    C L * levelPolynomial nodes weights (1 / L) =
      C L * Lagrange.nodal Finset.univ nodes - numerator nodes weights := by
  rw [levelPolynomial, mul_sub, ← mul_assoc, ← Polynomial.C_mul,
    mul_one_div_cancel hL, Polynomial.C_1, one_mul]

/-- Clearing denominators is justified at every actual nonpole. -/
theorem numerator_eval {n : ℕ} (nodes weights : Fin n → ℝ)
    (x : ℝ) (hx : ∀ i, x ≠ nodes i) :
    (numerator nodes weights).eval x =
      (Lagrange.nodal Finset.univ nodes).eval x * cauchy nodes weights x := by
  have hsplit (i : Fin n) :
      (Lagrange.nodal Finset.univ nodes).eval x =
        (x - nodes i) * (Lagrange.nodal (Finset.univ.erase i) nodes).eval x := by
    rw [Lagrange.eval_nodal, Lagrange.eval_nodal]
    exact (Finset.mul_prod_erase Finset.univ (fun j => x - nodes j)
      (Finset.mem_univ i)).symm
  rw [numerator, Polynomial.eval_finsetSum, cauchy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_C, hsplit i]
  calc
    weights i * (Lagrange.nodal (Finset.univ.erase i) nodes).eval x =
        (Lagrange.nodal (Finset.univ.erase i) nodes).eval x * weights i := mul_comm _ _
    _ = (Lagrange.nodal (Finset.univ.erase i) nodes).eval x *
        ((x - nodes i) * (weights i / (x - nodes i))) := by
      rw [mul_div_cancel₀ _ (sub_ne_zero.mpr (hx i))]
    _ = ((x - nodes i) * (Lagrange.nodal (Finset.univ.erase i) nodes).eval x) *
        (weights i / (x - nodes i)) := by ring

theorem eval_levelPolynomial {n : ℕ} (nodes weights : Fin n → ℝ)
    (A x : ℝ) (hx : ∀ i, x ≠ nodes i) :
    (levelPolynomial nodes weights A).eval x =
      (Lagrange.nodal Finset.univ nodes).eval x * (1 - A * cauchy nodes weights x) := by
  rw [levelPolynomial, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    numerator_eval nodes weights x hx]
  ring

section Nonempty

variable {m : ℕ} (nodes weights : Fin (m + 1) → ℝ)

private theorem erased_nodal_degree (i : Fin (m + 1)) :
    (Lagrange.nodal (Finset.univ.erase i) nodes).natDegree = m := by
  rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

theorem numerator_degree_le : (numerator nodes weights).natDegree ≤ m := by
  unfold numerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have h := Polynomial.natDegree_mul_le
    (p := C (weights i)) (q := Lagrange.nodal (Finset.univ.erase i) nodes)
  simpa only [Polynomial.natDegree_C, erased_nodal_degree nodes i, zero_add] using h

/-- Every erased nodal factor is monic of degree m, including m=0. -/
theorem numerator_coeff : (numerator nodes weights).coeff m = ∑ i, weights i := by
  simp only [numerator, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have h : (Lagrange.nodal (Finset.univ.erase i) nodes).coeff m = 1 := by
    simpa only [erased_nodal_degree nodes i] using
      (Lagrange.nodal_monic (s := Finset.univ.erase i) (v := nodes)).coeff_natDegree
  rw [h, mul_one]

theorem levelPolynomial_monic_degree (A : ℝ) :
    (levelPolynomial nodes weights A).Monic ∧
      (levelPolynomial nodes weights A).natDegree = m + 1 := by
  have hlow : (C A * numerator nodes weights).natDegree <
      (Lagrange.nodal Finset.univ nodes).natDegree := by
    have h := Polynomial.natDegree_mul_le (p := C A) (q := numerator nodes weights)
    simp only [Polynomial.natDegree_C, zero_add] at h
    have h' := h.trans (numerator_degree_le nodes weights)
    simpa only [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] using
      h'.trans_lt (Nat.lt_succ_self m)
  constructor
  · change (levelPolynomial nodes weights A).leadingCoeff = 1
    rw [levelPolynomial, Polynomial.leadingCoeff_sub_of_degree_lt (degree_lt_degree hlow)]
    exact Lagrange.nodal_monic
  · rw [levelPolynomial, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlow]
    simp

/-- Vieta is applied to the actual weighted polynomial, without normalized mass. -/
theorem sum_level_roots (A : ℝ) (u : Fin (m + 1) → ℝ)
    (heq : levelPolynomial nodes weights A = Lagrange.nodal Finset.univ u) :
    (∑ i, u i) = (∑ i, nodes i) + A * ∑ i, weights i := by
  have hW : (Lagrange.nodal Finset.univ nodes).coeff m = - ∑ i, nodes i := by
    simpa [Polynomial.nextCoeff] using CauchyLevelPolynomial.nodal_nextCoeff nodes
  have hU : (Lagrange.nodal Finset.univ u).coeff m = - ∑ i, u i := by
    simpa [Polynomial.nextCoeff] using CauchyLevelPolynomial.nodal_nextCoeff u
  have h := congrArg (fun p : ℝ[X] => p.coeff m) heq
  simp only [levelPolynomial, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    hW, hU, numerator_coeff nodes weights] at h
  linarith

/-- Actual positive levels supply every root and their total signed length. -/
theorem exists_positive_level_roots (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) (L : ℝ) (hL : 0 < L) :
    ∃ u : Fin (m + 1) → ℝ, StrictMono u ∧
      (∀ i, nodes i < u i) ∧
      (∀ i : Fin m, u i.castSucc < nodes i.succ) ∧
      (∀ i j, u i ≠ nodes j) ∧
      (∀ i, cauchy nodes weights (u i) = L) ∧
      levelPolynomial nodes weights (1 / L) = Lagrange.nodal Finset.univ u ∧
      (∑ i, (u i - nodes i)) = (∑ i, weights i) / L := by
  obtain ⟨r, hr, hrlevel⟩ :=
    (existsUnique_positive_level_right nodes weights hnodes hw L hL).exists
  have hinner : ∀ i : Fin m, ∃ x : ℝ,
      x ∈ Ioo (nodes i.castSucc) (nodes i.succ) ∧ cauchy nodes weights x = L :=
    fun i => (existsUnique_level_gap nodes weights hnodes hw i L).exists
  choose q hq hqlevel using hinner
  let u : Fin (m + 1) → ℝ := Fin.snoc q r
  have hleft : ∀ i, nodes i < u i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa only [u, Fin.snoc_last] using hr
    | cast i => simpa only [u, Fin.snoc_castSucc] using (hq i).1
  have hright : ∀ i : Fin m, u i.castSucc < nodes i.succ := by
    intro i
    simpa only [u, Fin.snoc_castSucc] using (hq i).2
  have hmono : StrictMono u := Fin.strictMono_iff_lt_succ.mpr
    (fun i => (hright i).trans (hleft i.succ))
  have havoid : ∀ i j, u i ≠ nodes j :=
    FiniteCauchyLevels.positive_array_avoids_nodes hnodes u hleft hright
  have hlevel : ∀ i, cauchy nodes weights (u i) = L := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa only [u, Fin.snoc_last] using hrlevel
    | cast i => simpa only [u, Fin.snoc_castSucc] using hqlevel i
  have hzero : ∀ i, (levelPolynomial nodes weights (1 / L)).eval (u i) = 0 := by
    intro i
    rw [eval_levelPolynomial nodes weights (1 / L) (u i) (havoid i),
      hlevel i, one_div_mul_cancel hL.ne', sub_self, mul_zero]
  obtain ⟨hmonic, hdegree⟩ := levelPolynomial_monic_degree nodes weights (1 / L)
  have hfactor : levelPolynomial nodes weights (1 / L) = Lagrange.nodal Finset.univ u :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic hmonic
      (InterlacingRoots.nodal_dvd_of_injective_roots hmono.injective hzero) (by
        simpa only [hdegree, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
          using (le_rfl : m + 1 ≤ m + 1))
  have hsum := sum_level_roots nodes weights (1 / L) u hfactor
  refine ⟨u, hmono, hleft, hright, havoid, hlevel, hfactor, ?_⟩
  rw [Finset.sum_sub_distrib, hsum]
  ring

/-- Negative levels are constructed independently, including the left exterior. -/
theorem exists_negative_level_roots (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) (L : ℝ) (hL : 0 < L) :
    ∃ v : Fin (m + 1) → ℝ, StrictMono v ∧
      (∀ i, v i < nodes i) ∧
      (∀ i : Fin m, nodes i.castSucc < v i.succ) ∧
      (∀ i j, v i ≠ nodes j) ∧
      (∀ i, cauchy nodes weights (v i) = -L) ∧
      levelPolynomial nodes weights (-(1 / L)) = Lagrange.nodal Finset.univ v ∧
      (∑ i, (nodes i - v i)) = (∑ i, weights i) / L := by
  obtain ⟨l, hl, hllevel⟩ :=
    (existsUnique_negative_level_left nodes weights hnodes hw (-L) (neg_neg_of_pos hL)).exists
  have hinner : ∀ i : Fin m, ∃ x : ℝ,
      x ∈ Ioo (nodes i.castSucc) (nodes i.succ) ∧ cauchy nodes weights x = -L :=
    fun i => (existsUnique_level_gap nodes weights hnodes hw i (-L)).exists
  choose q hq hqlevel using hinner
  let v : Fin (m + 1) → ℝ := Fin.cons l q
  have hright : ∀ i, v i < nodes i := by
    intro i
    cases i using Fin.cases with
    | zero => simpa only [v, Fin.cons_zero] using hl
    | succ i => simpa only [v, Fin.cons_succ] using (hq i).2
  have hleft : ∀ i : Fin m, nodes i.castSucc < v i.succ := by
    intro i
    simpa only [v, Fin.cons_succ] using (hq i).1
  have hmono : StrictMono v := Fin.strictMono_iff_lt_succ.mpr
    (fun i => (hright i.castSucc).trans (hleft i))
  have havoid : ∀ i j, v i ≠ nodes j :=
    FiniteCauchyLevels.negative_array_avoids_nodes hnodes v hright hleft
  have hlevel : ∀ i, cauchy nodes weights (v i) = -L := by
    intro i
    cases i using Fin.cases with
    | zero => simpa only [v, Fin.cons_zero] using hllevel
    | succ i => simpa only [v, Fin.cons_succ] using hqlevel i
  have hzero : ∀ i, (levelPolynomial nodes weights (-(1 / L))).eval (v i) = 0 := by
    intro i
    rw [eval_levelPolynomial nodes weights (-(1 / L)) (v i) (havoid i),
      hlevel i, neg_mul_neg, one_div_mul_cancel hL.ne', sub_self, mul_zero]
  obtain ⟨hmonic, hdegree⟩ := levelPolynomial_monic_degree nodes weights (-(1 / L))
  have hfactor : levelPolynomial nodes weights (-(1 / L)) = Lagrange.nodal Finset.univ v :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic hmonic
      (InterlacingRoots.nodal_dvd_of_injective_roots hmono.injective hzero) (by
        simpa only [hdegree, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
          using (le_rfl : m + 1 ≤ m + 1))
  have hsum := sum_level_roots nodes weights (-(1 / L)) v hfactor
  refine ⟨v, hmono, hright, hleft, havoid, hlevel, hfactor, ?_⟩
  rw [Finset.sum_sub_distrib, hsum]
  ring

private theorem cauchy_decreasing_gaps (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) : DecreasingGaps nodes (cauchy nodes weights) :=
  ⟨strictAntiOn_left nodes weights hnodes hw,
    strictAntiOn_right nodes weights hnodes hw,
    strictAntiOn_gap nodes weights hnodes hw⟩

private theorem positive_tail_bound_nonempty (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | L < cauchy nodes weights x} ≤ ENNReal.ofReal ((∑ i, weights i) / L) := by
  obtain ⟨u, _, hu, hugap, _, hul, _, hsum⟩ :=
    exists_positive_level_roots nodes weights hnodes hw L hL
  have hcover := positive_level_cover (cauchy_decreasing_gaps nodes weights hnodes hw)
    (fun x hx => cauchy_neg_left nodes weights hnodes hw hx) u hu hugap L hL hul
  rw [← hsum]
  apply volume_le_sum_lengths nodes u (fun i => (hu i).le) (range nodes) (finite_range nodes)
  intro x hx
  rcases hcover hx with h | h
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact Or.inr (mem_iUnion.mpr ⟨i, hi.1.le, hi.2.le⟩)

private theorem negative_tail_bound_nonempty (hnodes : StrictMono nodes)
    (hw : ∀ i, 0 < weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | cauchy nodes weights x < -L} ≤ ENNReal.ofReal ((∑ i, weights i) / L) := by
  obtain ⟨v, _, hv, hvgap, _, hvl, _, hsum⟩ :=
    exists_negative_level_roots nodes weights hnodes hw L hL
  have hcover := negative_level_cover (cauchy_decreasing_gaps nodes weights hnodes hw)
    (fun x hx => cauchy_pos_right nodes weights hnodes hw hx) v hv hvgap L hL hvl
  rw [← hsum]
  apply volume_le_sum_lengths v nodes (fun i => (hv i).le) (range nodes) (finite_range nodes)
  intro x hx
  rcases hcover hx with h | h
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact Or.inr (mem_iUnion.mpr ⟨i, hi.1.le, hi.2.le⟩)

end Nonempty

/-- The positive signed tail, for arbitrary finite positive weights and n=0. -/
theorem positive_tail_bound {n : ℕ} (nodes weights : Fin n → ℝ)
    (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | L < cauchy nodes weights x} ≤ ENNReal.ofReal ((∑ i, weights i) / L) := by
  cases n with
  | zero => simp [cauchy, not_lt_of_ge hL.le]
  | succ m => exact positive_tail_bound_nonempty nodes weights hnodes hw L hL

/-- The negative signed tail is proved without a reflection assumption. -/
theorem negative_tail_bound {n : ℕ} (nodes weights : Fin n → ℝ)
    (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | cauchy nodes weights x < -L} ≤ ENNReal.ofReal ((∑ i, weights i) / L) := by
  cases n with
  | zero => simp [cauchy, not_lt_of_ge (neg_nonpos.mpr hL.le)]
  | succ m => exact negative_tail_bound_nonempty nodes weights hnodes hw L hL

/-- The actual arbitrary-positive-atomic Boole upper estimate. -/
theorem upper_tail_bound {n : ℕ} (nodes weights : Fin n → ℝ)
    (hnodes : StrictMono nodes) (hw : ∀ i, 0 < weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | L < |cauchy nodes weights x|} ≤
      ENNReal.ofReal (2 * (∑ i, weights i) / L) := by
  have hp := positive_tail_bound nodes weights hnodes hw L hL
  have hn := negative_tail_bound nodes weights hnodes hw L hL
  have hm : 0 ≤ (∑ i, weights i) / L :=
    div_nonneg (Finset.sum_nonneg (fun i hi => (hw i).le)) hL.le
  have hcover : {x : ℝ | L < |cauchy nodes weights x|} ⊆
      {x | L < cauchy nodes weights x} ∪ {x | cauchy nodes weights x < -L} := by
    intro x hx
    change L < |cauchy nodes weights x| at hx
    by_cases h : 0 ≤ cauchy nodes weights x
    · left
      change L < cauchy nodes weights x
      simpa only [abs_of_nonneg h] using hx
    · right
      change cauchy nodes weights x < -L
      rw [abs_of_neg (lt_of_not_ge h)] at hx
      linarith
  calc
    volume _ ≤ volume ({x | L < cauchy nodes weights x} ∪
        {x | cauchy nodes weights x < -L}) := measure_mono hcover
    _ ≤ volume {x | L < cauchy nodes weights x} +
        volume {x | cauchy nodes weights x < -L} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((∑ i, weights i) / L) +
        ENNReal.ofReal ((∑ i, weights i) / L) := add_le_add hp hn
    _ = ENNReal.ofReal (2 * (∑ i, weights i) / L) := by
      rw [← ENNReal.ofReal_add hm hm]
      congr 1
      ring

end Jig133.AtomicCauchyBoole

end
end File_AtomicCauchyBoole

section File_AtomicCauchyFiniteFamily

/-!
# Boole's upper bound for an arbitrary finite nonnegative family

Repeated nodes are grouped by their actual fiber sums. Zero fibers are removed,
and the resulting finite support is enumerated in increasing order. The weighted
test-sum identity holds for every real test function, hence also for totalized
reciprocals at poles. No sorted representation is an input.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Jig133.AtomicCauchyFiniteFamily

open FiniteCauchyAnalysis

variable {ι : Type*} [Fintype ι]

/-- The whole mass of one node, retaining all repeated indices. -/
def fiberWeight (nodes weights : ι → ℝ) (y : ℝ) : ℝ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => nodes i = y), weights i

/-- The positive-mass fibers; nonnegative weights make every omitted fiber zero. -/
def positiveSupport (nodes weights : ι → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.image nodes).filter (fun y => 0 < fiberWeight nodes weights y)

/-- Increasing enumeration of the constructed support, including empty support. -/
def orderedNodes (nodes weights : ι → ℝ) :
    Fin (positiveSupport nodes weights).card → ℝ :=
  (positiveSupport nodes weights).orderEmbOfFin rfl

def orderedWeights (nodes weights : ι → ℝ) :
    Fin (positiveSupport nodes weights).card → ℝ :=
  fun i => fiberWeight nodes weights (orderedNodes nodes weights i)

theorem fiberWeight_nonneg (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (y : ℝ) : 0 ≤ fiberWeight nodes weights y := by
  classical
  exact Finset.sum_nonneg (fun i _ => hw i)

/-- Grouping preserves every weighted test sum, without any sign assumption. -/
theorem weighted_sum_grouped (nodes weights : ι → ℝ) (F : ℝ → ℝ) :
    (∑ y ∈ Finset.univ.image nodes, fiberWeight nodes weights y * F y) =
      ∑ i, weights i * F (nodes i) := by
  classical
  calc
    _ = ∑ y ∈ Finset.univ.image nodes,
        ∑ i ∈ Finset.univ.filter (fun i => nodes i = y), weights i * F (nodes i) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [fiberWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ.image nodes) (g := nodes)
      (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      (fun i => weights i * F (nodes i))

theorem weighted_sum_positiveSupport (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (F : ℝ → ℝ) :
    (∑ y ∈ positiveSupport nodes weights, fiberWeight nodes weights y * F y) =
      ∑ i, weights i * F (nodes i) := by
  classical
  calc
    _ = ∑ y ∈ Finset.univ.image nodes, fiberWeight nodes weights y * F y := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro y hy hnot
      have hn : ¬ 0 < fiberWeight nodes weights y := by
        intro hp
        exact hnot (Finset.mem_filter.mpr ⟨hy, hp⟩)
      have hz : fiberWeight nodes weights y = 0 :=
        le_antisymm (le_of_not_gt hn) (fiberWeight_nonneg nodes weights hw y)
      rw [hz, zero_mul]
    _ = _ := weighted_sum_grouped nodes weights F

theorem orderedNodes_strictMono (nodes weights : ι → ℝ) :
    StrictMono (orderedNodes nodes weights) :=
  ((positiveSupport nodes weights).orderEmbOfFin rfl).strictMono

theorem orderedWeights_pos (nodes weights : ι → ℝ) :
    ∀ i, 0 < orderedWeights nodes weights i := by
  classical
  intro i
  exact (Finset.mem_filter.mp
    ((positiveSupport nodes weights).orderEmbOfFin_mem rfl i)).2

/-- A constructed ordered family represents every weighted test sum. -/
theorem weighted_sum_ordered (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (F : ℝ → ℝ) :
    (∑ i, orderedWeights nodes weights i * F (orderedNodes nodes weights i)) =
      ∑ i, weights i * F (nodes i) := by
  classical
  calc
    _ = ∑ y ∈ positiveSupport nodes weights, fiberWeight nodes weights y * F y := by
      have hm := Finset.sum_map Finset.univ
        ((positiveSupport nodes weights).orderEmbOfFin rfl).toEmbedding
        (fun y => fiberWeight nodes weights y * F y)
      rw [Finset.map_orderEmbOfFin_univ] at hm
      exact hm.symm
    _ = _ := weighted_sum_positiveSupport nodes weights hw F

theorem sum_orderedWeights (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) :
    (∑ i, orderedWeights nodes weights i) = ∑ i, weights i := by
  simpa only [mul_one] using weighted_sum_ordered nodes weights hw (fun _ => 1)

/-- Pointwise equality for every real x, including every totalized pole. -/
theorem cauchy_ordered_eq (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (x : ℝ) :
    cauchy (orderedNodes nodes weights) (orderedWeights nodes weights) x =
      cauchy nodes weights x := by
  simpa only [cauchy, div_eq_mul_inv] using
    weighted_sum_ordered nodes weights hw (fun y => (x - y)⁻¹)

theorem positiveSupport_eq_empty_of_weights_zero (nodes weights : ι → ℝ)
    (hw : ∀ i, weights i = 0) : positiveSupport nodes weights = ∅ := by
  classical
  simp [positiveSupport, fiberWeight, hw]

theorem positive_tail_bound (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | L < cauchy nodes weights x} ≤
      ENNReal.ofReal ((∑ i, weights i) / L) := by
  have h := AtomicCauchyBoole.positive_tail_bound
    (orderedNodes nodes weights) (orderedWeights nodes weights)
    (orderedNodes_strictMono nodes weights) (orderedWeights_pos nodes weights) L hL
  simpa only [cauchy_ordered_eq nodes weights hw, sum_orderedWeights nodes weights hw] using h

theorem negative_tail_bound (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | cauchy nodes weights x < -L} ≤
      ENNReal.ofReal ((∑ i, weights i) / L) := by
  have h := AtomicCauchyBoole.negative_tail_bound
    (orderedNodes nodes weights) (orderedWeights nodes weights)
    (orderedNodes_strictMono nodes weights) (orderedWeights_pos nodes weights) L hL
  simpa only [cauchy_ordered_eq nodes weights hw, sum_orderedWeights nodes weights hw] using h

/-- The actual finite-family Boole bound, allowing repeats, zeros and empty index types. -/
theorem upper_tail_bound (nodes weights : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | L < |cauchy nodes weights x|} ≤
      ENNReal.ofReal (2 * (∑ i, weights i) / L) := by
  have h := AtomicCauchyBoole.upper_tail_bound
    (orderedNodes nodes weights) (orderedWeights nodes weights)
    (orderedNodes_strictMono nodes weights) (orderedWeights_pos nodes weights) L hL
  simpa only [cauchy_ordered_eq nodes weights hw, sum_orderedWeights nodes weights hw] using h

end Jig133.AtomicCauchyFiniteFamily

end
end File_AtomicCauchyFiniteFamily

section File_FiniteMeasureQuantization

/-!
# Actual finite-atomic approximations of finite real measures

The quantizer uses the finite nearest-point partitions in `SimpleFunc.approxOn`.
It converges at every real point. Its pushforwards have the exact original mass
and an explicit finite Dirac representation with nonnegative fiber weights.
Convergence of truncated Cauchy integrals is proved by dominated convergence
under the fixed original measure, excluding only the two truncation endpoints.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Jig133.FiniteMeasureQuantization

/-- The actual nearest-point finite-partition approximation to the identity. -/
def quantizer (n : ℕ) : SimpleFunc ℝ ℝ :=
  SimpleFunc.approxOn id measurable_id univ 0 (mem_univ 0) n

theorem measurable_quantizer (n : ℕ) : Measurable (quantizer n) :=
  (quantizer n).measurable

theorem finite_range_quantizer (n : ℕ) : (Set.range (quantizer n)).Finite :=
  (quantizer n).finite_range

theorem tendsto_quantizer (t : ℝ) :
    Tendsto (fun n => quantizer n t) atTop (𝓝 t) := by
  exact SimpleFunc.tendsto_approxOn measurable_id (mem_univ (0 : ℝ)) (by simp)

def quantized (σ : Measure ℝ) (n : ℕ) : Measure ℝ :=
  Measure.map (quantizer n) σ

instance finite_quantized (σ : Measure ℝ) [IsFiniteMeasure σ] (n : ℕ) :
    IsFiniteMeasure (quantized σ n) := by
  unfold quantized
  infer_instance

theorem quantized_univ (σ : Measure ℝ) (n : ℕ) :
    quantized σ n univ = σ univ := by
  rw [quantized, Measure.map_apply (measurable_quantizer n) MeasurableSet.univ]
  simp only [preimage_univ]

theorem quantized_real_univ (σ : Measure ℝ) (n : ℕ) :
    (quantized σ n).real univ = σ.real univ := by
  simp only [Measure.real, quantized_univ]

/-- Real nonnegative masses of the actual quantizer fibers, including zero fibers. -/
def weight (σ : Measure ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  σ.real ((quantizer n) ⁻¹' {z})

theorem weight_nonneg (σ : Measure ℝ) (n : ℕ) (z : ℝ) :
    0 ≤ weight σ n z := measureReal_nonneg

theorem sum_weight (σ : Measure ℝ) [IsFiniteMeasure σ] (n : ℕ) :
    ∑ z ∈ (quantizer n).range, weight σ n z = σ.real univ := by
  have h := congrArg ENNReal.toReal
    ((quantizer n).sum_range_measure_preimage_singleton σ)
  rw [ENNReal.toReal_sum (fun z _ => measure_ne_top σ _)] at h
  exact h

/-- The pushforward is literally a finite positive atomic measure. -/
theorem quantized_eq_sum_dirac (σ : Measure ℝ) [IsFiniteMeasure σ] (n : ℕ) :
    quantized σ n = ∑ z ∈ (quantizer n).range,
      ENNReal.ofReal (weight σ n z) • Measure.dirac z := by
  classical
  ext A hA
  have hpre : (quantizer n) ⁻¹' A =
      (quantizer n) ⁻¹' (↑((quantizer n).range.filter (fun z => z ∈ A)) : Set ℝ) := by
    ext t
    simp only [mem_preimage, Finset.mem_coe, Finset.mem_filter,
      (quantizer n).mem_range_self t, true_and]
  rw [quantized, Measure.map_apply (measurable_quantizer n) hA, hpre,
    ← (quantizer n).sum_measure_preimage_singleton,
    Measure.finsetSum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' z hA,
    weight, ofReal_measureReal]
  by_cases hzA : z ∈ A <;> simp [hzA]

/-- Every test composed with the finite-range quantizer is genuinely integrable;
the test itself need not be measurable or bounded on all of ℝ. -/
theorem integrable_comp_quantizer (σ : Measure ℝ) [IsFiniteMeasure σ]
    (n : ℕ) (g : ℝ → ℝ) : Integrable (fun t => g (quantizer n t)) σ :=
  ((quantizer n).map g).integrable_of_isFiniteMeasure

/-- Exact finite weighted-test identity, without a condition at the value zero. -/
theorem integral_comp_eq_sum (σ : Measure ℝ) [IsFiniteMeasure σ]
    (n : ℕ) (g : ℝ → ℝ) :
    (∫ t, g (quantizer n t) ∂σ) =
      ∑ z ∈ (quantizer n).range, weight σ n z * g z := by
  classical
  have hdecomp : (fun t => g (quantizer n t)) = fun t =>
      ∑ z ∈ (quantizer n).range,
        ((quantizer n) ⁻¹' {z}).indicator (fun _ : ℝ => g z) t := by
    funext t
    simp only [indicator_apply, mem_preimage, mem_singleton_iff, Finset.sum_ite_eq,
      (quantizer n).mem_range_self t, if_true]
  rw [hdecomp, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro z _hz
    rw [integral_indicator_const (g z) ((quantizer n).measurableSet_fiber z)]
    rfl
  · intro z _hz
    exact (integrable_const (g z)).indicator ((quantizer n).measurableSet_fiber z)

theorem integrable_quantized_test (σ : Measure ℝ) [IsFiniteMeasure σ]
    (n : ℕ) {g : ℝ → ℝ} (hg : Measurable g) : Integrable g (quantized σ n) := by
  exact (integrable_map_measure hg.aestronglyMeasurable
    (measurable_quantizer n).aemeasurable).mpr (integrable_comp_quantizer σ n g)

/-- The weighted sum is the actual integral of the test against the pushforward. -/
theorem integral_quantized_eq_sum (σ : Measure ℝ) [IsFiniteMeasure σ]
    (n : ℕ) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ t, g t ∂quantized σ n) =
      ∑ z ∈ (quantizer n).range, weight σ n z * g z := by
  rw [quantized, integral_map (measurable_quantizer n).aemeasurable
    hg.aestronglyMeasurable]
  exact integral_comp_eq_sum σ n g

/-- A bounded measurable test continuous at σ-almost every point has convergent
quantized integrals. The domination and convergence are under the fixed σ. -/
theorem tendsto_integral_of_ae_continuous (σ : Measure ℝ) [IsFiniteMeasure σ]
    {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ) (hbound : ∀ t, |g t| ≤ C)
    (hcont : ∀ᵐ t ∂σ, ContinuousAt g t) :
    Tendsto (fun n => ∫ t, g t ∂quantized σ n) atTop (𝓝 (∫ t, g t ∂σ)) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : ℝ => C)
    (fun n => ((quantizer n).map g).aestronglyMeasurable)
    (integrable_const C)
    (fun n => Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs, SimpleFunc.map_apply] using hbound (quantizer n t)))
    (hcont.mono (fun t ht => ht.tendsto.comp (tendsto_quantizer t)))
  have heq : (fun n => ∫ t, g t ∂quantized σ n) =
      (fun n => ∫ t, g (quantizer n t) ∂σ) := by
    funext n
    exact integral_map (measurable_quantizer n).aemeasurable hg.aestronglyMeasurable
  rw [heq]
  exact h

theorem tendsto_integral_continuous (σ : Measure ℝ) [IsFiniteMeasure σ]
    {g : ℝ → ℝ} (hg : Continuous g) (C : ℝ) (hbound : ∀ t, |g t| ≤ C) :
    Tendsto (fun n => ∫ t, g t ∂quantized σ n) atTop (𝓝 (∫ t, g t ∂σ)) :=
  tendsto_integral_of_ae_continuous σ hg.measurable C hbound
    (Eventually.of_forall (fun _t => hg.continuousAt))

/-- Strictly truncated reciprocal, with the actual value zero throughout the
central interval, including its endpoints and the pole. -/
def truncatedCauchy (x r t : ℝ) : ℝ :=
  if r < |x - t| then (x - t)⁻¹ else 0

theorem measurable_truncatedCauchy (x r : ℝ) : Measurable (truncatedCauchy x r) := by
  exact Measurable.ite
    (measurableSet_lt measurable_const (continuous_const.sub continuous_id).abs.measurable)
    (measurable_const.sub measurable_id).inv measurable_const

theorem abs_truncatedCauchy_le (x r : ℝ) (hr : 0 < r) (t : ℝ) :
    |truncatedCauchy x r t| ≤ 1 / r := by
  by_cases h : r < |x - t|
  · rw [truncatedCauchy, if_pos h, abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hr h.le
  · rw [truncatedCauchy, if_neg h, abs_zero]
    exact one_div_nonneg.mpr hr.le

theorem integrable_truncatedCauchy (σ : Measure ℝ) [IsFiniteMeasure σ]
    (x r : ℝ) (hr : 0 < r) : Integrable (truncatedCauchy x r) σ := by
  apply (integrable_const (1 / r)).mono' (measurable_truncatedCauchy x r).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs] using abs_truncatedCauchy_le x r hr t)

/-- The only possible discontinuities are the two truncation endpoints;
the apparent reciprocal pole belongs to an open region where the test is zero. -/
theorem continuousAt_truncatedCauchy (x r : ℝ) (hr : 0 < r) (t : ℝ)
    (ht : t ∉ ({x - r, x + r} : Set ℝ)) : ContinuousAt (truncatedCauchy x r) t := by
  have hne : |x - t| ≠ r := by
    intro heq
    apply ht
    rcases le_total 0 (x - t) with hp | hn
    · have h := (abs_of_nonneg hp).symm.trans heq
      have : t = x - r := by linarith
      simp only [this, mem_insert_iff, mem_singleton_iff, true_or]
    · have h := (abs_of_nonpos hn).symm.trans heq
      have : t = x + r := by linarith
      simp only [this, mem_insert_iff, mem_singleton_iff, or_true]
  have hd : Continuous (fun y : ℝ => |x - y|) :=
    (continuous_const.sub continuous_id).abs
  rcases lt_or_gt_of_ne hne with hin | hout
  · have he : ∀ᶠ y in 𝓝 t, |x - y| < r := (isOpen_lt hd continuous_const).mem_nhds hin
    apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) t from continuousAt_const).congr
    filter_upwards [he] with y hy
    simp only [truncatedCauchy, if_neg (not_lt.mpr hy.le)]
  · have hz : x - t ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hout
      linarith
    have he : ∀ᶠ y in 𝓝 t, r < |x - y| := (isOpen_lt continuous_const hd).mem_nhds hout
    have hi : ContinuousAt (fun y : ℝ => (x - y)⁻¹) t :=
      (continuous_const.sub continuous_id).continuousAt.inv₀ hz
    apply hi.congr
    filter_upwards [he] with y hy
    simp only [truncatedCauchy, if_pos hy]

/-- Actual truncated-Cauchy convergence for every positive radius with null
endpoint pair, allowing arbitrary other atoms and zero original mass. -/
theorem tendsto_integral_truncatedCauchy (σ : Measure ℝ) [IsFiniteMeasure σ]
    (x r : ℝ) (hr : 0 < r) (hboundary : σ ({x - r, x + r} : Set ℝ) = 0) :
    Tendsto (fun n => ∫ t, truncatedCauchy x r t ∂quantized σ n)
      atTop (𝓝 (∫ t, truncatedCauchy x r t ∂σ)) := by
  apply tendsto_integral_of_ae_continuous σ (measurable_truncatedCauchy x r)
    (1 / r) (abs_truncatedCauchy_le x r hr)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hboundary] with t ht
  exact continuousAt_truncatedCauchy x r hr t ht

/-- The same convergence expressed using the explicit finite atomic weights. -/
theorem tendsto_sum_truncatedCauchy (σ : Measure ℝ) [IsFiniteMeasure σ]
    (x r : ℝ) (hr : 0 < r) (hboundary : σ ({x - r, x + r} : Set ℝ) = 0) :
    Tendsto (fun n => ∑ z ∈ (quantizer n).range,
      weight σ n z * truncatedCauchy x r z)
      atTop (𝓝 (∫ t, truncatedCauchy x r t ∂σ)) := by
  have h := tendsto_integral_truncatedCauchy σ x r hr hboundary
  have heq : (fun n => ∫ t, truncatedCauchy x r t ∂quantized σ n) =
      (fun n => ∑ z ∈ (quantizer n).range,
        weight σ n z * truncatedCauchy x r z) := by
    funext n
    exact integral_quantized_eq_sum σ n (measurable_truncatedCauchy x r)
  rw [heq] at h
  exact h

end Jig133.FiniteMeasureQuantization

end
end File_FiniteMeasureQuantization

section File_FiniteCauchyTruncationTransfer

/-!
# Transfer of strict truncated-Cauchy weak bounds from finite atomic measures

All rational truncation endpoints are null outside one explicitly constructed
countable set of centers. Every strict real-radius exceedance has a positive
rational witness, proved by dominated convergence from larger radii, including
endpoint atoms. The actual P41 quantizers then give an eventual-set inclusion
and the set form of Fatou's argument. The final theorem still takes the uniform
finite-atomic weak estimate as an explicit input; it does not prove Cotlar.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Jig133.FiniteCauchyTruncationTransfer

open FiniteMeasureQuantization

/-- Actual atoms, without an atomlessness premise. -/
def atomSet (σ : Measure ℝ) : Set ℝ := {a | 0 < σ {a}}

/-- Rational translates of actual atoms contain every bad rational endpoint
center. Both signs and the zero rational are deliberately included. -/
def exceptionalCenters (σ : Measure ℝ) : Set ℝ :=
  ⋃ q : ℚ, ((fun a : ℝ => a + (q : ℝ)) '' atomSet σ) ∪
    ((fun a : ℝ => a - (q : ℝ)) '' atomSet σ)

theorem countable_atomSet (σ : Measure ℝ) [IsFiniteMeasure σ] :
    (atomSet σ).Countable := by
  exact Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := σ) (As := fun a : ℝ => {a})
    (fun a => measurableSet_singleton a)
    (fun _ _ h => disjoint_singleton.mpr h)

theorem countable_exceptionalCenters (σ : Measure ℝ) [IsFiniteMeasure σ] :
    (exceptionalCenters σ).Countable := by
  apply countable_iUnion
  intro q
  exact ((countable_atomSet σ).image (fun a : ℝ => a + (q : ℝ))).union
    ((countable_atomSet σ).image (fun a : ℝ => a - (q : ℝ)))

theorem endpoint_pair_null_of_not_mem (σ : Measure ℝ) (x : ℝ)
    (hx : x ∉ exceptionalCenters σ) (q : ℚ) :
    σ ({x - (q : ℝ), x + (q : ℝ)} : Set ℝ) = 0 := by
  have hl : σ {x - (q : ℝ)} = 0 := by
    by_contra hn
    apply hx
    apply mem_iUnion.mpr
    refine ⟨q, Or.inl ?_⟩
    exact ⟨x - (q : ℝ), pos_iff_ne_zero.mpr hn, sub_add_cancel _ _⟩
  have hr : σ {x + (q : ℝ)} = 0 := by
    by_contra hn
    apply hx
    apply mem_iUnion.mpr
    refine ⟨q, Or.inr ?_⟩
    exact ⟨x + (q : ℝ), pos_iff_ne_zero.mpr hn, add_sub_cancel_right _ _⟩
  rw [show ({x - (q : ℝ), x + (q : ℝ)} : Set ℝ) =
    {x - (q : ℝ)} ∪ {x + (q : ℝ)} by ext t; simp [or_comm]]
  exact measure_union_null hl hr

/-- One Lebesgue null set suffices for every rational truncation radius. -/
theorem ae_rational_endpoint_pairs_null (σ : Measure ℝ) [IsFiniteMeasure σ] :
    ∀ᵐ x ∂volume, ∀ q : ℚ,
      σ ({x - (q : ℝ), x + (q : ℝ)} : Set ℝ) = 0 := by
  filter_upwards [(countable_exceptionalCenters σ).ae_notMem volume] with x hx
  exact endpoint_pair_null_of_not_mem σ x hx

/-- Actual simultaneous rational-radius convergence for the constructed
quantizers, with the common exceptional set depending only on σ. -/
theorem ae_rational_quantized_convergence (σ : Measure ℝ) [IsFiniteMeasure σ] :
    ∀ᵐ x ∂volume, ∀ q : ℚ, 0 < (q : ℝ) →
      Tendsto (fun n => ∫ t, truncatedCauchy x (q : ℝ) t ∂quantized σ n)
        atTop (𝓝 (∫ t, truncatedCauchy x (q : ℝ) t ∂σ)) := by
  filter_upwards [ae_rational_endpoint_pairs_null σ] with x hx
  intro q hq
  exact tendsto_integral_truncatedCauchy σ x (q : ℝ) hq (hx q)

/-- Approaching a cutoff from above preserves its strict exclusion, even at
the two endpoints. No null-endpoint hypothesis is used here. -/
theorem tendsto_truncatedCauchy_of_radii_from_above (x r t : ℝ)
    (u : ℕ → ℝ) (hu : ∀ n, r ≤ u n) (hlim : Tendsto u atTop (𝓝 r)) :
    Tendsto (fun n => truncatedCauchy x (u n) t) atTop
      (𝓝 (truncatedCauchy x r t)) := by
  by_cases ht : r < |x - t|
  · have he : ∀ᶠ n in atTop, u n < |x - t| := hlim.eventually (Iio_mem_nhds ht)
    have heq : (fun _n : ℕ => truncatedCauchy x r t) =ᶠ[atTop]
        (fun n => truncatedCauchy x (u n) t) := by
      filter_upwards [he] with n hn
      simp only [truncatedCauchy, if_pos ht, if_pos hn]
    exact tendsto_const_nhds.congr' heq
  · have heq : (fun _n : ℕ => truncatedCauchy x r t) =ᶠ[atTop]
        (fun n => truncatedCauchy x (u n) t) := by
      apply Eventually.of_forall
      intro n
      have hn : ¬ u n < |x - t| := not_lt.mpr ((le_of_not_gt ht).trans (hu n))
      simp only [truncatedCauchy, if_neg ht, if_neg hn]
    exact tendsto_const_nhds.congr' heq

/-- Genuine integral convergence for larger cutoffs: the finite measure
integrates the constant bound 1/r, including when σ has endpoint atoms. -/
theorem tendsto_integral_of_radii_from_above (σ : Measure ℝ) [IsFiniteMeasure σ]
    (x r : ℝ) (hr : 0 < r) (u : ℕ → ℝ) (hu : ∀ n, r ≤ u n)
    (hlim : Tendsto u atTop (𝓝 r)) :
    Tendsto (fun n => ∫ t, truncatedCauchy x (u n) t ∂σ) atTop
      (𝓝 (∫ t, truncatedCauchy x r t ∂σ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _t : ℝ => 1 / r)
  · intro n
    exact (measurable_truncatedCauchy x (u n)).aestronglyMeasurable
  · exact integrable_const (1 / r)
  · intro n
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs]
    exact (abs_truncatedCauchy_le x (u n) (hr.trans_le (hu n)) t).trans
      (one_div_le_one_div_of_le hr (hu n))
  · exact Eventually.of_forall (fun t =>
      tendsto_truncatedCauchy_of_radii_from_above x r t u hu hlim)

/-- Literal strict maximal superlevel set; no real supremum or principal value
is used. Every integral at a positive radius is genuinely integrable. -/
def maximalSet (σ : Measure ℝ) (L : ℝ) : Set ℝ :=
  {x | ∃ r : ℝ, 0 < r ∧ L < |∫ t, truncatedCauchy x r t ∂σ|}

/-- Every strict real-radius exceedance has a positive rational witness. -/
theorem mem_maximalSet_iff_rational (σ : Measure ℝ) [IsFiniteMeasure σ]
    (L x : ℝ) :
    x ∈ maximalSet σ L ↔
      ∃ q : ℚ, 0 < (q : ℝ) ∧ L < |∫ t, truncatedCauchy x (q : ℝ) t ∂σ| := by
  constructor
  · rintro ⟨r, hr, hv⟩
    obtain ⟨u, _hanti, hu, hlim⟩ := Real.exists_seq_rat_strictAnti_tendsto r
    have hi := tendsto_integral_of_radii_from_above σ x r hr
      (fun n => (u n : ℝ)) (fun n => (hu n).le) hlim
    have ha := (continuous_abs.tendsto (∫ t, truncatedCauchy x r t ∂σ)).comp hi
    have he : ∀ᶠ n in atTop, L < |∫ t, truncatedCauchy x (u n : ℝ) t ∂σ| :=
      ha.eventually (Ioi_mem_nhds hv)
    obtain ⟨n, hn⟩ := he.exists
    exact ⟨u n, hr.trans (hu n), hn⟩
  · rintro ⟨q, hq, hv⟩
    exact ⟨(q : ℝ), hq, hv⟩

/-- The set version of Fatou's argument, derived through increasing tail
intersections. It applies to outer measures of arbitrary sets. -/
theorem measure_eventual_mem_le (A : ℕ → Set ℝ) (B : ℝ≥0∞)
    (hB : ∀ n, volume (A n) ≤ B) :
    volume {x | ∀ᶠ n in atTop, x ∈ A n} ≤ B := by
  let tails (N : ℕ) : Set ℝ := {x | ∀ n, N ≤ n → x ∈ A n}
  have hmono : Monotone tails := by
    intro N K hNK x hx n hKn
    exact hx n (hNK.trans hKn)
  have heq : {x | ∀ᶠ n in atTop, x ∈ A n} = ⋃ N, tails N := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, eventually_atTop, tails]
  rw [heq, hmono.measure_iUnion]
  apply iSup_le
  intro N
  exact (measure_mono (show tails N ⊆ A N from fun _x hx => hx N le_rfl)).trans (hB N)

/-- The actual maximal set lies, away from a null set of centers, in the
eventual membership set of the actual finite-atomic quantized maximal sets. -/
theorem ae_mem_eventually_quantized (σ : Measure ℝ) [IsFiniteMeasure σ] (L : ℝ) :
    ∀ᵐ x ∂volume, x ∈ maximalSet σ L →
      ∀ᶠ n in atTop, x ∈ maximalSet (quantized σ n) L := by
  filter_upwards [ae_rational_quantized_convergence σ] with x hx
  intro hmem
  obtain ⟨q, hq, hv⟩ := (mem_maximalSet_iff_rational σ L x).mp hmem
  have ha := (continuous_abs.tendsto (∫ t, truncatedCauchy x (q : ℝ) t ∂σ)).comp
    (hx q hq)
  have he : ∀ᶠ n in atTop, L < |∫ t, truncatedCauchy x (q : ℝ) t ∂quantized σ n| :=
    ha.eventually (Ioi_mem_nhds hv)
  exact he.mono (fun n hn => ⟨(q : ℝ), hq, hn⟩)

/-- A uniform bound on the actual quantized maximal sets transfers to the
original measure. The eventual-set inclusion is proved, not an input. -/
theorem maximalSet_volume_le_of_quantized_bounds (σ : Measure ℝ) [IsFiniteMeasure σ]
    (L : ℝ) (B : ℝ≥0∞) (hB : ∀ n, volume (maximalSet (quantized σ n) L) ≤ B) :
    volume (maximalSet σ L) ≤ B := by
  have hsub : maximalSet σ L ≤ᵐ[volume]
      {x | ∀ᶠ n in atTop, x ∈ maximalSet (quantized σ n) L} :=
    ae_mem_eventually_quantized σ L
  exact (measure_mono_ae hsub).trans
    (measure_eventual_mem_le (fun n => maximalSet (quantized σ n) L) B hB)

/-- The remaining finite-atomic analytic input, expressed as genuine finite
weighted truncated sums with nonnegative weights, including zero weights and
empty support. This definition asserts no such estimate on its own. -/
def AtomicWeakBound (C : ℝ) : Prop :=
  ∀ (s : Finset ℝ) (w : ℝ → ℝ), (∀ z ∈ s, 0 ≤ w z) →
    ∀ L : ℝ, 0 < L →
      volume {x : ℝ | ∃ r : ℝ, 0 < r ∧
        L < |∑ z ∈ s, w z * truncatedCauchy x r z|} ≤
        ENNReal.ofReal (C * (∑ z ∈ s, w z) / L)

/-- Actual finite-atomic-to-finite-measure weak-bound transfer. Cotlar or any
other proof of `AtomicWeakBound C` remains an explicit separate obligation. -/
theorem maximalSet_volume_le_of_atomic_weak_bound (C : ℝ) (hAtomic : AtomicWeakBound C)
    (σ : Measure ℝ) [IsFiniteMeasure σ] (L : ℝ) (hL : 0 < L) :
    volume (maximalSet σ L) ≤ ENNReal.ofReal (C * σ.real univ / L) := by
  apply maximalSet_volume_le_of_quantized_bounds σ L _
  intro n
  have h := hAtomic (quantizer n).range (weight σ n)
    (fun z _hz => weight_nonneg σ n z) L hL
  have heq : maximalSet (quantized σ n) L =
      {x : ℝ | ∃ r : ℝ, 0 < r ∧
        L < |∑ z ∈ (quantizer n).range, weight σ n z * truncatedCauchy x r z|} := by
    ext x
    constructor
    · rintro ⟨r, hr, hv⟩
      refine ⟨r, hr, ?_⟩
      rw [integral_quantized_eq_sum σ n (measurable_truncatedCauchy x r)] at hv
      exact hv
    · rintro ⟨r, hr, hv⟩
      refine ⟨r, hr, ?_⟩
      rw [integral_quantized_eq_sum σ n (measurable_truncatedCauchy x r)]
      exact hv
  rw [heq]
  simpa only [sum_weight] using h

end Jig133.FiniteCauchyTruncationTransfer

end
end File_FiniteCauchyTruncationTransfer

section File_AtomicCauchyCotlar

/-!
# A finite positive atomic maximal-Cauchy bound by a median argument

The dyadic inverse-square estimate is proved for actual nonnegative weights.
It controls the change of the far Cauchy sum in a half-radius neighborhood.
Boole's theorem applied to the actual near weights then forces a large full
Cauchy value on three quarters of that neighborhood. Applying maximal density
to the restriction of Lebesgue measure to a Boole superlevel set proves the
numerical constant 168. No maximal-transform estimate is an input.

All indexed nodes, including repeats and zero weights, are retained. The near
and far decomposition is pointwise even at totalized near poles; every far
denominator used for subtraction is explicitly nonzero.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Jig133.AtomicCauchyCotlar

open FiniteCauchyAnalysis FiniteMeasureQuantization

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

private def partialSquare (d w : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i, if d i < r then w i / (d i) ^ 2 else 0

private theorem partialSquare_step (d w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A r : ℝ) (hr : 0 < r)
    (hmass : (∑ i, if d i ≤ 2 * r then w i else 0) ≤ A * (2 * r)) :
    partialSquare d w (2 * r) ≤ partialSquare d w r + 2 * A / r := by
  have hpoint (i : ι) :
      (if d i < 2 * r then w i / (d i) ^ 2 else 0) ≤
        (if d i < r then w i / (d i) ^ 2 else 0) +
          (if d i ≤ 2 * r then w i / r ^ 2 else 0) := by
    by_cases h2 : d i < 2 * r
    · by_cases h1 : d i < r
      · simp only [if_pos h2, if_pos h1, if_pos h2.le]
        exact le_add_of_nonneg_right (div_nonneg (hw i) (sq_nonneg r))
      · have hri : r ≤ d i := le_of_not_gt h1
        simp only [if_pos h2, if_neg h1, if_pos h2.le, zero_add]
        exact div_le_div_of_nonneg_left (hw i) (sq_pos_of_pos hr)
          ((sq_le_sq₀ hr.le (hr.le.trans hri)).mpr hri)
    · simp only [if_neg h2]
      have hwi := hw i
      split_ifs <;> positivity
  have hconstant : (∑ i, if d i ≤ 2 * r then w i / r ^ 2 else 0) ≤
      2 * A / r := by
    calc
      _ = (∑ i, if d i ≤ 2 * r then w i else 0) / r ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ ≤ (A * (2 * r)) / r ^ 2 :=
        div_le_div_of_nonneg_right hmass (sq_nonneg r)
      _ = 2 * A / r := by field_simp [hr.ne']
  calc
    partialSquare d w (2 * r) ≤ partialSquare d w r +
        (∑ i, if d i ≤ 2 * r then w i / r ^ 2 else 0) := by
      unfold partialSquare
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ partialSquare d w r + 2 * A / r := add_le_add le_rfl hconstant

private theorem partialSquare_dyadic (d w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a A : ℝ) (ha : 0 < a) (hzero : ∀ i, d i < a → w i = 0)
    (hmass : ∀ r : ℝ, 0 < r →
      (∑ i, if d i ≤ r then w i else 0) ≤ A * r) (N : ℕ) :
    partialSquare d w (a * 2 ^ N) ≤ 4 * A / a - 4 * A / (a * 2 ^ N) := by
  induction N with
  | zero =>
      have hz : partialSquare d w a = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : d i < a
        · simp only [if_pos hi, hzero i hi, zero_div]
        · exact if_neg hi
      simpa only [pow_zero, mul_one, hz, sub_self] using (le_refl (0 : ℝ))
  | succ N ih =>
      have hr : 0 < a * (2 : ℝ) ^ N := mul_pos ha (pow_pos (by norm_num) N)
      have hrad : a * (2 : ℝ) ^ (N + 1) = 2 * (a * 2 ^ N) := by
        rw [pow_succ]
        ring
      rw [hrad]
      calc
        partialSquare d w (2 * (a * 2 ^ N)) ≤ partialSquare d w (a * 2 ^ N) +
            2 * A / (a * 2 ^ N) :=
          partialSquare_step d w hw A _ hr
            (hmass _ (mul_pos (by norm_num) hr))
        _ ≤ (4 * A / a - 4 * A / (a * 2 ^ N)) + 2 * A / (a * 2 ^ N) :=
          add_le_add ih le_rfl
        _ = 4 * A / a - 4 * A / (2 * (a * 2 ^ N)) := by
          have hscale : 4 * A / (2 * (a * 2 ^ N)) = 2 * A / (a * 2 ^ N) := by
            field_simp [ha.ne', pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0)]
            ring
          rw [hscale]
          ring

/-- Weighted finite dyadic summation, including weights zero below the cutoff.
There is no inverse-square estimate among the hypotheses. -/
theorem weighted_inverse_square (d w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (hzero : ∀ i, d i < a → w i = 0)
    (hmass : ∀ r : ℝ, 0 < r →
      (∑ i, if d i ≤ r then w i else 0) ≤ A * r) :
    (∑ i, w i / (d i) ^ 2) ≤ 4 * A / a := by
  rcases (Finset.univ : Finset ι).eq_empty_or_nonempty with he | hn
  · rw [he, Finset.sum_empty]
    positivity
  · obtain ⟨i₀, _, hmax⟩ := (Finset.univ : Finset ι).exists_max_image d hn
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (d i₀ / a) (by norm_num : (1 : ℝ) < 2)
    have hupper : d i₀ < a * (2 : ℝ) ^ N := by
      have := (div_lt_iff₀ ha).mp hN
      nlinarith
    have hall (i : ι) : d i < a * (2 : ℝ) ^ N :=
      (hmax i (Finset.mem_univ i)).trans_lt hupper
    have heq : partialSquare d w (a * (2 : ℝ) ^ N) = ∑ i, w i / (d i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact if_pos (hall i)
    have hb := partialSquare_dyadic d w hw a A ha hzero hmass N
    rw [heq] at hb
    exact hb.trans (sub_le_self _ (by positivity))

/-- Literal weighted mass in the closed radius-r interval around x. -/
def ballMass (nodes weights : ι → ℝ) (x r : ℝ) : ℝ :=
  ∑ i, if |x - nodes i| ≤ r then weights i else 0

/-- The actual far inverse-square sum is bounded by the all-radius density. -/
theorem tail_inverse_square (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (x r b : ℝ) (hr : 0 < r) (hb : 0 ≤ b)
    (hdensity : ∀ R : ℝ, 0 < R → ballMass nodes weights x R ≤ 2 * b * R) :
    (∑ i, if r < |x - nodes i| then weights i / (x - nodes i) ^ 2 else 0) ≤
      8 * b / r := by
  let v : ι → ℝ := fun i => if r < |x - nodes i| then weights i else 0
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    dsimp [v]
    split_ifs
    · exact hw i
    · exact le_rfl
  have hz : ∀ i, |x - nodes i| < r → v i = 0 := by
    intro i hi
    exact if_neg (not_lt_of_ge hi.le)
  have hm (R : ℝ) (hR : 0 < R) :
      (∑ i, if |x - nodes i| ≤ R then v i else 0) ≤ (2 * b) * R := by
    apply le_trans _ (hdensity R hR)
    apply Finset.sum_le_sum
    intro i _
    change (if |x - nodes i| ≤ R then v i else 0) ≤
      (if |x - nodes i| ≤ R then weights i else 0)
    by_cases hiR : |x - nodes i| ≤ R
    · simp only [if_pos hiR]
      dsimp [v]
      split_ifs
      · exact le_rfl
      · exact hw i
    · simp only [if_neg hiR, le_refl]
  have h := weighted_inverse_square (fun i => |x - nodes i|) v hv r (2 * b)
    hr (mul_nonneg (by norm_num) hb) hz hm
  have heq : (∑ i, v i / |x - nodes i| ^ 2) =
      ∑ i, if r < |x - nodes i| then weights i / (x - nodes i) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    split_ifs <;> simp only [sq_abs, zero_div]
  rw [heq] at h
  convert h using 1
  ring

/-- The same strict-cutoff kernel as the checked atomic-to-measure transfer. -/
def truncatedSum (nodes weights : ι → ℝ) (x r : ℝ) : ℝ :=
  ∑ i, weights i * truncatedCauchy x r (nodes i)

def nearWeights (nodes weights : ι → ℝ) (x r : ℝ) : ι → ℝ :=
  fun i => if |x - nodes i| ≤ r then weights i else 0

def farWeights (nodes weights : ι → ℝ) (x r : ℝ) : ι → ℝ :=
  fun i => if r < |x - nodes i| then weights i else 0

theorem cauchy_near_add_far (nodes weights : ι → ℝ) (x r y : ℝ) :
    cauchy nodes weights y = cauchy nodes (nearWeights nodes weights x r) y +
      cauchy nodes (farWeights nodes weights x r) y := by
  unfold cauchy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r < |x - nodes i|
  · simp only [nearWeights, farWeights, if_pos hi, if_neg (not_le.mpr hi), zero_div, zero_add]
  · simp only [nearWeights, farWeights, if_neg hi, if_pos (le_of_not_gt hi), zero_div, add_zero]

theorem cauchy_far_at_center (nodes weights : ι → ℝ) (x r : ℝ) :
    cauchy nodes (farWeights nodes weights x r) x = truncatedSum nodes weights x r := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r < |x - nodes i| <;>
    simp only [farWeights, truncatedCauchy, hi, if_true, if_false,
      mul_zero, div_eq_mul_inv, zero_mul]

/-- Every far pole stays nonzero throughout the closed half-radius interval. -/
theorem far_denominator (x y t r : ℝ) (hr : 0 < r)
    (ht : r < |x - t|) (hy : |y - x| ≤ r / 2) :
    y ≠ t ∧ |x - t| ≤ 2 * |y - t| := by
  have htriangle := abs_sub_le x y t
  rw [abs_sub_comm x y] at htriangle
  have hp : 0 < |y - t| := by linarith
  exact ⟨sub_ne_zero.mp (abs_pos.mp hp), by linarith⟩

theorem reciprocal_difference (x y t r : ℝ) (hr : 0 < r)
    (ht : r < |x - t|) (hy : |y - x| ≤ r / 2) :
    |1 / (y - t) - 1 / (x - t)| ≤ 2 * |y - x| * (1 / (x - t) ^ 2) := by
  have hfar := far_denominator x y t r hr ht hy
  have hdx : 0 < |x - t| := hr.trans ht
  have hdy : 0 < |y - t| := abs_pos.mpr (sub_ne_zero.mpr hfar.1)
  have heq : 1 / (y - t) - 1 / (x - t) = (x - y) / ((y - t) * (x - t)) := by
    field_simp [sub_ne_zero.mpr hfar.1, abs_pos.mp hdx]
    ring
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hfar.2 hdx.le) (abs_nonneg (y - x))
  calc
    _ = |y - x| / (|y - t| * |x - t|) := by
      rw [heq, abs_div, abs_mul, abs_sub_comm x y]
    _ ≤ (2 * |y - x|) / |x - t| ^ 2 := by
      apply (div_le_div_iff₀ (mul_pos hdy hdx) (sq_pos_of_pos hdx)).mpr
      nlinarith
    _ = 2 * |y - x| * (1 / (x - t) ^ 2) := by rw [sq_abs]; ring

/-- Actual Cotlar far-field comparison, from weighted density alone. -/
theorem far_difference_le (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (x r b y : ℝ) (hr : 0 < r) (hb : 0 ≤ b)
    (hdensity : ∀ R : ℝ, 0 < R → ballMass nodes weights x R ≤ 2 * b * R)
    (hy : |y - x| ≤ r / 2) :
    |cauchy nodes (farWeights nodes weights x r) y - truncatedSum nodes weights x r| ≤
      8 * b := by
  have ht := tail_inverse_square nodes weights hw x r b hr hb hdensity
  rw [← cauchy_far_at_center]
  unfold cauchy
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |farWeights nodes weights x r i / (y - nodes i) -
        farWeights nodes weights x r i / (x - nodes i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * |y - x| *
        (if r < |x - nodes i| then weights i / (x - nodes i) ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : r < |x - nodes i|
      · simp only [farWeights, if_pos hi]
        have heq : weights i / (y - nodes i) - weights i / (x - nodes i) =
            weights i * (1 / (y - nodes i) - 1 / (x - nodes i)) := by ring
        rw [heq, abs_mul, abs_of_nonneg (hw i)]
        have h := mul_le_mul_of_nonneg_left
          (reciprocal_difference x y (nodes i) r hr hi hy) (hw i)
        convert h using 1
        ring
      · simp only [farWeights, if_neg hi, zero_div, sub_self, abs_zero, mul_zero, le_refl]
    _ = (2 * |y - x|) *
        ∑ i, if r < |x - nodes i| then weights i / (x - nodes i) ^ 2 else 0 := by
      rw [Finset.mul_sum]
    _ ≤ (2 * |y - x|) * (8 * b / r) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ r * (8 * b / r) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 8 * b := by field_simp [hr.ne']

/-- Boole applied to the actual near weights removes at most a quarter of the
length-r centered interval. -/
theorem near_exception_volume (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (x r b : ℝ) (_hr : 0 < r) (hb : 0 < b)
    (hmass : ballMass nodes weights x r ≤ 2 * b * r) :
    volume {y : ℝ | 16 * b < |cauchy nodes (nearWeights nodes weights x r) y|} ≤
      ENNReal.ofReal (r / 4) := by
  have hw' : ∀ i, 0 ≤ nearWeights nodes weights x r i := by
    intro i
    dsimp [nearWeights]
    split_ifs
    · exact hw i
    · exact le_rfl
  have h := AtomicCauchyFiniteFamily.upper_tail_bound nodes (nearWeights nodes weights x r)
    hw' (16 * b) (by positivity)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by positivity : 0 < 16 * b)).mpr
  change (∑ i, if |x - nodes i| ≤ r then weights i else 0) ≤ 2 * b * r at hmass
  change 2 * (∑ i, if |x - nodes i| ≤ r then weights i else 0) ≤ (r / 4) * (16 * b)
  nlinarith

private theorem large_full_value (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (x r b L y : ℝ) (hr : 0 < r) (hb : 0 ≤ b)
    (hdensity : ∀ R : ℝ, 0 < R → ballMass nodes weights x R ≤ 2 * b * R)
    (hy : |y - x| ≤ r / 2) (hscale : 24 * b ≤ L / 2)
    (hlarge : L < |truncatedSum nodes weights x r|)
    (hnear : |cauchy nodes (nearWeights nodes weights x r) y| ≤ 16 * b) :
    L / 2 < |cauchy nodes weights y| := by
  have hf := far_difference_le nodes weights hw x r b y hr hb hdensity hy
  have hsplit := cauchy_near_add_far nodes weights x r y
  have hbound : |truncatedSum nodes weights x r| ≤
      |cauchy nodes weights y| + |cauchy nodes (nearWeights nodes weights x r) y| + 8 * b := by
    calc
      _ = |(cauchy nodes weights y - cauchy nodes (nearWeights nodes weights x r) y) +
          (truncatedSum nodes weights x r - cauchy nodes (farWeights nodes weights x r) y)| := by
        congr 1
        linarith
      _ ≤ |cauchy nodes weights y - cauchy nodes (nearWeights nodes weights x r) y| +
          |truncatedSum nodes weights x r - cauchy nodes (farWeights nodes weights x r) y| :=
        abs_add_le _ _
      _ ≤ _ := add_le_add (abs_sub _ _) (by rwa [abs_sub_comm] at hf)
  linarith

/-- A large strict truncation at a density-good center forces a large full
Cauchy sum on at least three quarters of its centered interval. -/
theorem median_mass_lower (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (x r L : ℝ) (hr : 0 < r) (hL : 0 < L)
    (hdensity : ∀ R : ℝ, 0 < R → ballMass nodes weights x R ≤ 2 * (L / 48) * R)
    (hlarge : L < |truncatedSum nodes weights x r|) :
    3 * r / 4 ≤ volume.real (Icc (x - r / 2) (x + r / 2) ∩
      {y : ℝ | L / 2 < |cauchy nodes weights y|}) := by
  let I : Set ℝ := Icc (x - r / 2) (x + r / 2)
  let A : Set ℝ := {y : ℝ | L / 2 < |cauchy nodes weights y|}
  let N : Set ℝ := {y : ℝ | 16 * (L / 48) <
    |cauchy nodes (nearWeights nodes weights x r) y|}
  have hN : volume N ≤ ENNReal.ofReal (r / 4) :=
    near_exception_volume nodes weights hw x r (L / 48) hr (by positivity) (hdensity r hr)
  have hNfinite : volume N ≠ ∞ := ne_of_lt (hN.trans_lt ENNReal.ofReal_lt_top)
  have hIAfinite : volume (I ∩ A) ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_left).trans_lt (isCompact_Icc.measure_lt_top))
  have hcover : I ⊆ (I ∩ A) ∪ N := by
    intro y hy
    by_cases hn : y ∈ N
    · exact Or.inr hn
    · refine Or.inl ⟨hy, ?_⟩
      have hxy : |y - x| ≤ r / 2 := by
        rw [abs_le]
        change x - r / 2 ≤ y ∧ y ≤ x + r / 2 at hy
        constructor <;> linarith [hy.1, hy.2]
      exact large_full_value nodes weights hw x r (L / 48) L y hr (by positivity)
        hdensity hxy (by linarith) hlarge (le_of_not_gt hn)
  have hvol : volume I ≤ volume (I ∩ A) + volume N :=
    (measure_mono hcover).trans (measure_union_le _ _)
  have hre := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hIAfinite, hNfinite⟩) hvol
  rw [ENNReal.toReal_add hIAfinite hNfinite] at hre
  have hnr : (volume N).toReal ≤ r / 4 := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r / 4)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hN
  have hir : (volume I).toReal = r := by
    rw [show volume I = ENNReal.ofReal r by
      dsimp [I]
      rw [Real.volume_Icc]
      congr 1
      ring]
    exact ENNReal.toReal_ofReal hr.le
  change 3 * r / 4 ≤ (volume (I ∩ A)).toReal
  linarith

/-- The actual positive atomic measure used for maximal density. -/
def atomicMeasure (nodes weights : ι → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (weights i) • Measure.dirac (nodes i)

instance finite_atomicMeasure (nodes weights : ι → ℝ) : IsFiniteMeasure (atomicMeasure nodes weights) := by
  constructor
  have hu : atomicMeasure nodes weights univ = ∑ i, ENNReal.ofReal (weights i) := by
    simp [atomicMeasure, Measure.finsetSum_apply]
  rw [hu]
  exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.ofReal_lt_top)

theorem atomicMeasure_apply (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (s : Set ℝ) (hs : MeasurableSet s) :
    atomicMeasure nodes weights s = ENNReal.ofReal (∑ i, if nodes i ∈ s then weights i else 0) := by
  rw [atomicMeasure, Measure.finsetSum_apply,
    ENNReal.ofReal_sum_of_nonneg
      (f := fun i : ι => if nodes i ∈ s then weights i else 0) (fun i _ => by
      split_ifs
      · exact hw i
      · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  by_cases hi : nodes i ∈ s <;> simp [hi]

theorem atomicMeasure_real_univ (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i) :
    (atomicMeasure nodes weights).real univ = ∑ i, weights i := by
  rw [Measure.real, atomicMeasure_apply nodes weights hw univ MeasurableSet.univ]
  simp only [mem_univ, if_true]
  exact ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hw i))

theorem atomicMeasure_Icc (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i) (x r : ℝ) :
    atomicMeasure nodes weights (Icc (x - r) (x + r)) =
      ENNReal.ofReal (ballMass nodes weights x r) := by
  rw [atomicMeasure_apply nodes weights hw _ measurableSet_Icc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : nodes i ∈ Icc (x - r) (x + r) ↔ |x - nodes i| ≤ r := by
    rw [mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [heq]

def densitySet (nodes weights : ι → ℝ) (b : ℝ) : Set ℝ :=
  {x | ∃ r : ℝ, 0 < r ∧ 2 * b * r < ballMass nodes weights x r}

theorem densitySet_volume_le (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (b : ℝ) (hb : 0 < b) :
    volume (densitySet nodes weights b) ≤ ENNReal.ofReal (3 * (∑ i, weights i) / b) := by
  have hsub : densitySet nodes weights b ⊆ {x : ℝ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal (b * (2 * r)) < atomicMeasure nodes weights (Icc (x - r) (x + r))} := by
    rintro x ⟨r, hr, hd⟩
    refine ⟨r, hr, ?_⟩
    rw [atomicMeasure_Icc nodes weights hw]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity : 0 ≤ b * (2 * r))).mpr
    nlinarith
  have h := FiniteMeasureMaximalDensity.maximal_density_bound_three (atomicMeasure nodes weights) b hb
  rw [atomicMeasure_real_univ nodes weights hw] at h
  exact (measure_mono hsub).trans h

/-- A numerical bound on the actual maximal truncated sum, with no ordering,
support restriction, positive-total-mass premise or transform oracle. -/
theorem maximal_tail_bound (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | ∃ r : ℝ, 0 < r ∧ L < |truncatedSum nodes weights x r|} ≤
      ENNReal.ofReal (168 * (∑ i, weights i) / L) := by
  let m : ℝ := ∑ i, weights i
  have hm : 0 ≤ m := Finset.sum_nonneg (fun i _ => hw i)
  let A : Set ℝ := {y : ℝ | L / 2 < |cauchy nodes weights y|}
  have hA : volume A ≤ ENNReal.ofReal (4 * m / L) := by
    have h := AtomicCauchyFiniteFamily.upper_tail_bound nodes weights hw (L / 2) (by positivity)
    calc
      volume A ≤ ENNReal.ofReal (2 * (∑ i, weights i) / (L / 2)) := h
      _ = ENNReal.ofReal (4 * m / L) := by
        congr 1
        dsimp [m]
        ring
  let η : Measure ℝ := volume.restrict A
  let : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
    (ne_of_lt (hA.trans_lt ENNReal.ofReal_lt_top))
  have hη : η.real univ ≤ 4 * m / L := by
    rw [show η.real univ = volume.real A from measureReal_restrict_apply_univ A]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hA).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  let E : Set ℝ := {x : ℝ | ∃ r : ℝ, 0 < r ∧
    ENNReal.ofReal ((1 / 2 : ℝ) * (2 * r)) < η (Icc (x - r) (x + r))}
  have hsub : {x : ℝ | ∃ r : ℝ, 0 < r ∧ L < |truncatedSum nodes weights x r|} ⊆
      densitySet nodes weights (L / 48) ∪ E := by
    rintro x ⟨r, hr, hv⟩
    by_cases hd : x ∈ densitySet nodes weights (L / 48)
    · exact Or.inl hd
    · right
      have hgood : ∀ R : ℝ, 0 < R → ballMass nodes weights x R ≤ 2 * (L / 48) * R := by
        intro R hR
        by_contra hn
        exact hd ⟨R, hR, lt_of_not_ge hn⟩
      have hmed := median_mass_lower nodes weights hw x r L hr hL hgood hv
      refine ⟨r / 2, by positivity, ?_⟩
      rw [← ofReal_measureReal (μ := η)]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity :
        0 ≤ (1 / 2 : ℝ) * (2 * (r / 2)))).mpr
      have hident : η.real (Icc (x - r / 2) (x + r / 2)) =
          volume.real (Icc (x - r / 2) (x + r / 2) ∩ A) :=
        measureReal_restrict_apply measurableSet_Icc
      rw [hident]
      change 3 * r / 4 ≤ volume.real (Icc (x - r / 2) (x + r / 2) ∩ A) at hmed
      linarith
  have hD := densitySet_volume_le nodes weights hw (L / 48) (by positivity)
  have hE : volume E ≤ ENNReal.ofReal (24 * m / L) := by
    apply (FiniteMeasureMaximalDensity.maximal_density_bound_three η (1 / 2) (by norm_num)).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      3 * η.real univ / (1 / 2 : ℝ) = 6 * η.real univ := by ring
      _ ≤ 6 * (4 * m / L) := mul_le_mul_of_nonneg_left hη (by norm_num)
      _ = 24 * m / L := by ring
  calc
    _ ≤ volume (densitySet nodes weights (L / 48) ∪ E) := measure_mono hsub
    _ ≤ volume (densitySet nodes weights (L / 48)) + volume E := measure_union_le _ _
    _ ≤ ENNReal.ofReal (3 * m / (L / 48)) + ENNReal.ofReal (24 * m / L) := add_le_add hD hE
    _ = ENNReal.ofReal (3 * m / (L / 48) + 24 * m / L) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal (168 * m / L) := by congr 1; ring

/-- The previously explicit atomic obligation now has a numerical witness. -/
theorem atomicWeakBound_168 : FiniteCauchyTruncationTransfer.AtomicWeakBound 168 := by
  intro s w hw L hL
  have h := maximal_tail_bound (fun i : s => (i : ℝ)) (fun i : s => w i)
    (fun i => hw i i.property) L hL
  have hsum (x r : ℝ) :
      truncatedSum (fun i : s => (i : ℝ)) (fun i : s => w i) x r =
        ∑ z ∈ s, w z * truncatedCauchy x r z := by
    change (∑ i : s, (fun z : ℝ => w z * truncatedCauchy x r z) (i : ℝ)) = _
    exact Finset.sum_coe_sort s (fun z => w z * truncatedCauchy x r z)
  have hmass : (∑ i : s, w i) = ∑ z ∈ s, w z := Finset.sum_coe_sort s w
  simpa only [hsum, hmass] using h

/-- The checked rational-cutoff/Fatou transfer now applies with a proved
numerical atomic bound, including arbitrary finite measures with atoms. -/
theorem finite_measure_maximal_bound (σ : Measure ℝ) [IsFiniteMeasure σ]
    (L : ℝ) (hL : 0 < L) :
    volume (FiniteCauchyTruncationTransfer.maximalSet σ L) ≤
      ENNReal.ofReal (168 * σ.real univ / L) :=
  FiniteCauchyTruncationTransfer.maximalSet_volume_le_of_atomic_weak_bound
    168 atomicWeakBound_168 σ L hL

end Jig133.AtomicCauchyCotlar

end
end File_AtomicCauchyCotlar

section File_SoftCauchyKernel

/-!
# A bounded softened Cauchy kernel and its literal truncation error

The kernel remains continuous at a real pole when h is positive. The comparison
uses the actual strict symmetric cutoff, including its boundary points.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace Jig133.SoftCauchyKernel

def kernel (h x t : ℝ) : ℝ := (x - t) / ((x - t) ^ 2 + h ^ 2)

theorem denominator_pos (h x t : ℝ) (hh : 0 < h) :
    0 < (x - t) ^ 2 + h ^ 2 := by positivity

theorem abs_le (h x t : ℝ) (hh : 0 < h) : |kernel h x t| ≤ 1 / h := by
  rw [kernel, abs_div, abs_of_pos (denominator_pos h x t hh)]
  apply (div_le_div_iff₀ (denominator_pos h x t hh) hh).mpr
  nlinarith [sq_nonneg (|x - t| - h), sq_abs (x - t)]

theorem continuous_kernel (h x : ℝ) (hh : 0 < h) : Continuous (kernel h x) := by
  unfold kernel
  exact (continuous_const.sub continuous_id).div
    (((continuous_const.sub continuous_id).pow 2).add continuous_const)
    (fun t => (denominator_pos h x t hh).ne')

theorem integrable_kernel (σ : Measure ℝ) [IsFiniteMeasure σ]
    (h x : ℝ) (hh : 0 < h) : Integrable (kernel h x) σ := by
  apply (integrable_const (1 / h)).mono' (continuous_kernel h x hh).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs] using abs_le h x t hh)

theorem reciprocal_error (h x t : ℝ) (hh : 0 < h) (hne : x - t ≠ 0) :
    |kernel h x t - (x - t)⁻¹| ≤ h / (x - t) ^ 2 := by
  have hd := denominator_pos h x t hh
  have hs : 0 < |x - t| := abs_pos.mpr hne
  have he : kernel h x t - (x - t)⁻¹ =
      -(h ^ 2) / ((x - t) * ((x - t) ^ 2 + h ^ 2)) := by
    unfold kernel
    field_simp [hne, hd.ne']
    ring
  rw [he, abs_div, abs_neg, abs_of_nonneg (sq_nonneg h), abs_mul, abs_of_pos hd]
  apply (div_le_div_iff₀ (mul_pos hs hd) (sq_pos_of_ne_zero hne)).mpr
  have hb : h * |x - t| ≤ (x - t) ^ 2 + h ^ 2 := by
    nlinarith [sq_nonneg (|x - t| - h), sq_abs (x - t)]
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hh.le hs.le)
  nlinarith [sq_abs (x - t)]

theorem truncation_error (h x t : ℝ) (hh : 0 < h) :
    |kernel h x t - FiniteMeasureQuantization.truncatedCauchy x h t| ≤
      (if |x - t| ≤ h then 1 / h else 0) +
      (if h < |x - t| then h / (x - t) ^ 2 else 0) := by
  by_cases ht : h < |x - t|
  · simp only [FiniteMeasureQuantization.truncatedCauchy, if_pos ht,
      if_neg (not_le.mpr ht), zero_add]
    exact reciprocal_error h x t hh (abs_pos.mp (hh.trans ht))
  · simp only [FiniteMeasureQuantization.truncatedCauchy, if_neg ht,
      if_pos (le_of_not_gt ht), sub_zero, add_zero]
    exact abs_le h x t hh

end Jig133.SoftCauchyKernel

end
end File_SoftCauchyKernel

section File_CayleySoftTransform

/-!
# The actual softened transform of one root measure

Differentiate the previously proved upper-half-plane potential identity.
The derivative bound 1/h is uniform in the integration variable and center.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Jig133.CayleySoftTransform
open SoftCauchyKernel

def logKernel (h x t : ℝ) : ℝ :=
  Real.log ‖(x : ℂ) + (h : ℂ) * Complex.I - (t : ℂ)‖

theorem logKernel_eq (h x t : ℝ) :
    logKernel h x t = Real.log ((x - t) ^ 2 + h ^ 2) / 2 := by
  have hn : ‖(x : ℂ) + (h : ℂ) * Complex.I - (t : ℂ)‖ ^ 2 = (x - t) ^ 2 + h ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  calc
    _ = Real.log (‖(x : ℂ) + (h : ℂ) * Complex.I - (t : ℂ)‖ ^ 2) / 2 := by
      rw [Real.log_pow]
      unfold logKernel
      ring
    _ = _ := by rw [hn]

theorem hasDerivAt_logKernel (h x t : ℝ) (hh : 0 < h) :
    HasDerivAt (fun y => logKernel h y t) (kernel h x t) x := by
  have hd := ((((hasDerivAt_id x).sub_const t).pow 2).add_const (h ^ 2)).log
    (denominator_pos h x t hh).ne'
  have he := hd.div_const 2
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at he
  have hv : 2 * (x - t) / ((x - t) ^ 2 + h ^ 2) / 2 = kernel h x t := by
    unfold kernel
    ring
  rw [hv] at he
  simpa only [logKernel_eq] using he

theorem integrable_logKernel (a s h x : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    Integrable (logKernel h x) (CayleyRootMeasure.rootMeasure a s) := by
  apply CayleyRootPotential.integrable_log_norm a s
    ((x : ℂ) + (h : ℂ) * Complex.I) hs
  simpa using hh

theorem integral_logKernel (a s h x : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    (∫ t, logKernel h x t ∂CayleyRootMeasure.rootMeasure a s) = logKernel (h + s) x a := by
  unfold logKernel
  rw [CayleyRootPotential.integral_log_norm a s
    ((x : ℂ) + (h : ℂ) * Complex.I) hs (by simpa using hh)]
  congr 2
  push_cast
  ring

theorem integral_kernel (a s h x : ℝ) (hs : 0 ≤ s) (hh : 0 < h) :
    (∫ t, kernel h x t ∂CayleyRootMeasure.rootMeasure a s) = kernel (h + s) x a := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := CayleyRootMeasure.rootMeasure a s)
    (F := fun y t => logKernel h y t) (F' := fun y t => kernel h y t)
    (bound := fun _t : ℝ => 1 / h) (s := univ) (x₀ := x)
    (show univ ∈ 𝓝 x from univ_mem)
    (Eventually.of_forall (fun y =>
      (CayleyRootPotential.measurable_log_norm ((y : ℂ) + (h : ℂ) * Complex.I)).aestronglyMeasurable))
    (integrable_logKernel a s h x hs hh.le)
    (continuous_kernel h x hh).aestronglyMeasurable
    (Eventually.of_forall (fun t y _ => by
      simpa only [Real.norm_eq_abs] using SoftCauchyKernel.abs_le h y t hh))
    (integrable_const (1 / h))
    (Eventually.of_forall (fun t y _ => hasDerivAt_logKernel h y t hh))
  have he : (fun y => ∫ t, logKernel h y t ∂CayleyRootMeasure.rootMeasure a s) =
      (fun y => logKernel (h + s) y a) := funext (fun y => integral_logKernel a s h y hs hh.le)
  rw [he] at hd
  exact hd.2.unique (hasDerivAt_logKernel (h + s) x a (add_pos_of_pos_of_nonneg hh hs))

end Jig133.CayleySoftTransform

end
end File_CayleySoftTransform

section File_AtomicSoftCauchy

/-!
# The softened Cauchy maximal bound for arbitrary finite positive atoms

All heights share the same density and truncated-maximal exceptional sets.
The proof retains repeated nodes and zero weights.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Jig133.AtomicSoftCauchy
open AtomicCauchyCotlar
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

def softSum (nodes weights : ι → ℝ) (x h : ℝ) : ℝ :=
  ∑ i, weights i * SoftCauchyKernel.kernel h x (nodes i)

theorem comparison (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (x h b : ℝ) (hh : 0 < h) (hb : 0 ≤ b)
    (hd : ∀ R : ℝ, 0 < R → ballMass nodes weights x R ≤ 2 * b * R) :
    |softSum nodes weights x h - truncatedSum nodes weights x h| ≤ 10 * b := by
  have hp (i : ι) :
      |weights i * SoftCauchyKernel.kernel h x (nodes i) -
        weights i * FiniteMeasureQuantization.truncatedCauchy x h (nodes i)| ≤
      (if |x - nodes i| ≤ h then weights i / h else 0) +
      (if h < |x - nodes i| then h * (weights i / (x - nodes i) ^ 2) else 0) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw i)]
    have he := mul_le_mul_of_nonneg_left
      (SoftCauchyKernel.truncation_error h x (nodes i) hh) (hw i)
    apply he.trans_eq
    split_ifs <;> ring
  have hn : ballMass nodes weights x h / h ≤ 2 * b := by
    apply (div_le_iff₀ hh).mpr
    exact hd h hh
  have hf : h * (∑ i, if h < |x - nodes i| then weights i / (x - nodes i) ^ 2 else 0) ≤
      8 * b := by
    have he := mul_le_mul_of_nonneg_left (tail_inverse_square nodes weights hw x h b hh hb hd) hh.le
    calc
      _ ≤ h * (8 * b / h) := he
      _ = 8 * b := by field_simp [hh.ne']
  calc
    _ = |∑ i, (weights i * SoftCauchyKernel.kernel h x (nodes i) -
        weights i * FiniteMeasureQuantization.truncatedCauchy x h (nodes i))| := by
      rw [Finset.sum_sub_distrib]
      rfl
    _ ≤ ∑ i, |weights i * SoftCauchyKernel.kernel h x (nodes i) -
        weights i * FiniteMeasureQuantization.truncatedCauchy x h (nodes i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((if |x - nodes i| ≤ h then weights i / h else 0) +
        (if h < |x - nodes i| then h * (weights i / (x - nodes i) ^ 2) else 0)) :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = ballMass nodes weights x h / h +
        h * (∑ i, if h < |x - nodes i| then weights i / (x - nodes i) ^ 2 else 0) := by
      rw [Finset.sum_add_distrib, ballMass, Finset.sum_div, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> split_ifs <;> simp
    _ ≤ 2 * b + 8 * b := add_le_add hn hf
    _ = 10 * b := by ring

theorem maximal_bound (nodes weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | ∃ h : ℝ, 0 < h ∧ L < |softSum nodes weights x h|} ≤
      ENNReal.ofReal (396 * (∑ i, weights i) / L) := by
  let T : Set ℝ := {x | ∃ h : ℝ, 0 < h ∧ L / 2 < |truncatedSum nodes weights x h|}
  have hsub : {x : ℝ | ∃ h : ℝ, 0 < h ∧ L < |softSum nodes weights x h|} ⊆
      densitySet nodes weights (L / 20) ∪ T := by
    rintro x ⟨h, hh, hv⟩
    by_cases hx : x ∈ densitySet nodes weights (L / 20)
    · exact Or.inl hx
    · right
      have hd : ∀ R : ℝ, 0 < R → ballMass nodes weights x R ≤ 2 * (L / 20) * R := by
        intro R hR
        exact le_of_not_gt (fun hbad => hx ⟨R, hR, hbad⟩)
      have he := comparison nodes weights hw x h (L / 20) hh (by positivity) hd
      refine ⟨h, hh, ?_⟩
      have ht := abs_add_le (softSum nodes weights x h - truncatedSum nodes weights x h)
        (truncatedSum nodes weights x h)
      simp only [sub_add_cancel] at ht
      linarith
  have hm : 0 ≤ ∑ i, weights i := Finset.sum_nonneg (fun i _ => hw i)
  calc
    _ ≤ volume (densitySet nodes weights (L / 20) ∪ T) := measure_mono hsub
    _ ≤ volume (densitySet nodes weights (L / 20)) + volume T := measure_union_le _ _
    _ ≤ ENNReal.ofReal (3 * (∑ i, weights i) / (L / 20)) +
        ENNReal.ofReal (168 * (∑ i, weights i) / (L / 2)) :=
      add_le_add (densitySet_volume_le nodes weights hw (L / 20) (by positivity))
        (maximal_tail_bound nodes weights hw (L / 2) (by positivity))
    _ = ENNReal.ofReal (396 * (∑ i, weights i) / L) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Jig133.AtomicSoftCauchy

end
end File_AtomicSoftCauchy

section File_FiniteSoftCauchy

/-!
# A maximal softened Cauchy bound for every finite positive measure

Bounded continuous kernels pass through the actual finite quantizers at every
center and every fixed height. Strict exceedances give eventual membership.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Jig133.FiniteSoftCauchy
open FiniteMeasureQuantization

def transform (σ : Measure ℝ) (h x : ℝ) : ℝ :=
  ∫ t, SoftCauchyKernel.kernel h x t ∂σ

def maximalSet (σ : Measure ℝ) (L : ℝ) : Set ℝ :=
  {x | ∃ h : ℝ, 0 < h ∧ L < |transform σ h x|}

theorem tendsto_quantized (σ : Measure ℝ) [IsFiniteMeasure σ]
    (h x : ℝ) (hh : 0 < h) :
    Tendsto (fun n => transform (quantized σ n) h x) atTop (𝓝 (transform σ h x)) :=
  tendsto_integral_continuous σ (SoftCauchyKernel.continuous_kernel h x hh)
    (1 / h) (fun t => SoftCauchyKernel.abs_le h x t hh)

theorem quantized_bound (σ : Measure ℝ) [IsFiniteMeasure σ]
    (n : ℕ) (L : ℝ) (hL : 0 < L) :
    volume (maximalSet (quantized σ n) L) ≤ ENNReal.ofReal (396 * σ.real univ / L) := by
  classical
  let s := (quantizer n).range
  have h := AtomicSoftCauchy.maximal_bound (fun i : s => (i : ℝ))
    (fun i : s => weight σ n i) (fun i => weight_nonneg σ n i) L hL
  have hsum (x h : ℝ) (hh : 0 < h) :
      AtomicSoftCauchy.softSum (fun i : s => (i : ℝ)) (fun i : s => weight σ n i) x h =
        transform (quantized σ n) h x := by
    rw [transform, integral_quantized_eq_sum σ n (SoftCauchyKernel.continuous_kernel h x hh).measurable]
    exact Finset.sum_coe_sort s (fun z => weight σ n z * SoftCauchyKernel.kernel h x z)
  have hmass : (∑ i : s, weight σ n i) = σ.real univ := by
    rw [Finset.sum_coe_sort]
    exact sum_weight σ n
  have hset : {x : ℝ | ∃ h : ℝ, 0 < h ∧
      L < |AtomicSoftCauchy.softSum (fun i : s => (i : ℝ)) (fun i : s => weight σ n i) x h|} =
      maximalSet (quantized σ n) L := by
    ext x
    constructor
    · rintro ⟨h, hh, hv⟩
      exact ⟨h, hh, by rwa [hsum x h hh] at hv⟩
    · rintro ⟨h, hh, hv⟩
      exact ⟨h, hh, by rwa [hsum x h hh]⟩
  rwa [hset, hmass] at h

theorem mem_eventually_quantized (σ : Measure ℝ) [IsFiniteMeasure σ]
    (L x : ℝ) (hx : x ∈ maximalSet σ L) :
    ∀ᶠ n in atTop, x ∈ maximalSet (quantized σ n) L := by
  obtain ⟨h, hh, hv⟩ := hx
  have hc := (continuous_abs.tendsto (transform σ h x)).comp (tendsto_quantized σ h x hh)
  exact (hc.eventually (Ioi_mem_nhds hv)).mono (fun n hn => ⟨h, hh, hn⟩)

theorem maximal_bound (σ : Measure ℝ) [IsFiniteMeasure σ] (L : ℝ) (hL : 0 < L) :
    volume (maximalSet σ L) ≤ ENNReal.ofReal (396 * σ.real univ / L) := by
  apply (measure_mono (show maximalSet σ L ⊆
    {x | ∀ᶠ n in atTop, x ∈ maximalSet (quantized σ n) L} from
      fun x hx => mem_eventually_quantized σ L x hx)).trans
  exact FiniteCauchyTruncationTransfer.measure_eventual_mem_le
    (fun n => maximalSet (quantized σ n) L) _ (fun n => quantized_bound σ n L hL)

end Jig133.FiniteSoftCauchy

end
end File_FiniteSoftCauchy

section File_CayleyLogMoment

/-!
# A genuine logarithmic moment of the Cayley root measure

The potential at i dominates log(1+|t|). This proves the logarithmic moment
needed for later Fubini estimates, without presuming a finite first moment.
-/

open MeasureTheory
noncomputable section
namespace Jig133.CayleyLogMoment
open CayleyRootMeasure CayleyRootPotential

theorem norm_I_sub_real_ge_one (t : ℝ) : 1 ≤ ‖Complex.I - (t : ℂ)‖ := by
  simpa using Complex.abs_im_le_norm (Complex.I - (t : ℂ))

theorem log_moment_bound (t : ℝ) :
    0 ≤ Real.log (1 + |t|) ∧
    Real.log (1 + |t|) ≤ Real.log 2 + Real.log ‖Complex.I - (t : ℂ)‖ := by
  have h1 := norm_I_sub_real_ge_one t
  have ht : |t| ≤ ‖Complex.I - (t : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (Complex.I - (t : ℂ))
  have hn : 0 < ‖Complex.I - (t : ℂ)‖ := by linarith
  refine ⟨Real.log_nonneg (by linarith [abs_nonneg t]), ?_⟩
  calc
    Real.log (1 + |t|) ≤ Real.log (2 * ‖Complex.I - (t : ℂ)‖) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log ‖Complex.I - (t : ℂ)‖ :=
      Real.log_mul two_ne_zero hn.ne'

/-- Integrability of the actual nonnegative logarithmic moment, including
the zero-scale probability. No moment hypothesis is supplied. -/
theorem integrable_log_one_add_abs (a s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun t : ℝ => Real.log (1 + |t|)) (rootMeasure a s) := by
  have hg : Integrable (fun t : ℝ => Real.log 2 + Real.log ‖Complex.I - (t : ℂ)‖)
      (rootMeasure a s) :=
    (integrable_const _).add (integrable_log_norm a s Complex.I hs (by simp))
  have hm : Measurable (fun t : ℝ => Real.log (1 + |t|)) :=
    Real.measurable_log.comp (measurable_const.add continuous_abs.measurable)
  exact hg.mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => (log_moment_bound t).1))
    (Filter.Eventually.of_forall (fun t => (log_moment_bound t).2))

theorem integral_log_one_add_abs_le (a s : ℝ) (hs : 0 ≤ s) :
    (∫ t : ℝ, Real.log (1 + |t|) ∂rootMeasure a s) ≤
      Real.log 2 + Real.log ‖Complex.I - (a : ℂ) + (s : ℂ) * Complex.I‖ := by
  have hc : Integrable (fun _ : ℝ => Real.log 2) (rootMeasure a s) := integrable_const _
  have hi := integrable_log_norm a s Complex.I hs (by simp)
  have hsum : Integrable (fun t : ℝ => Real.log 2 + Real.log ‖Complex.I - (t : ℂ)‖)
      (rootMeasure a s) := hc.add hi
  have h := integral_mono (integrable_log_one_add_abs a s hs) hsum
    (fun t => (log_moment_bound t).2)
  rw [integral_add hc hi, integral_log_norm a s Complex.I hs (by simp)] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

end Jig133.CayleyLogMoment

end
end File_CayleyLogMoment

section File_PolynomialRootMeasure

/-!
# The positive measure of the full complex polynomial root multiset

Every occurrence of a root contributes its actual Cayley probability. No
root is removed and no nodup hypothesis is imposed. Product logarithms are
used only at nonzero polynomial evaluations, with the leading coefficient
retained. All integrability statements concern the literal totalized log.
-/

open Set MeasureTheory Polynomial
open scoped ENNReal

noncomputable section

namespace Jig133.PolynomialRootMeasure

/-- One positive probability for each occurrence, including real roots. -/
def ofRoots (r : Multiset ℂ) : Measure ℝ :=
  (r.map (fun ζ => CayleyRootMeasure.rootMeasure ζ.re |ζ.im|)).sum

@[simp] theorem ofRoots_zero : ofRoots 0 = 0 := by simp [ofRoots]

@[simp] theorem ofRoots_cons (ζ : ℂ) (r : Multiset ℂ) :
    ofRoots (ζ ::ₘ r) = CayleyRootMeasure.rootMeasure ζ.re |ζ.im| + ofRoots r := by
  simp only [ofRoots, Multiset.map_cons, Multiset.sum_cons]

theorem ofRoots_mass (r : Multiset ℂ) : ofRoots r univ = (r.card : ℝ≥0∞) := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons ζ r ih =>
    simp only [ofRoots_cons, Measure.add_apply, CayleyRootMeasure.rootMeasure_mass,
      ih, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    exact add_comm _ _

instance ofRoots_finite (r : Multiset ℂ) : IsFiniteMeasure (ofRoots r) where
  measure_univ_lt_top := by
    rw [ofRoots_mass]
    exact ENNReal.natCast_lt_top _

/-- This measure is selected from Q alone, before any evaluation point. -/
def rootMeasure (Q : ℂ[X]) : Measure ℝ := ofRoots Q.roots

instance rootMeasure_finite (Q : ℂ[X]) : IsFiniteMeasure (rootMeasure Q) :=
  ofRoots_finite Q.roots

/-- Algebraic closure counts every root with its actual multiplicity.
The equality also holds for the zero polynomial, whose natDegree is zero. -/
theorem rootMeasure_mass (Q : ℂ[X]) : rootMeasure Q univ = (Q.natDegree : ℝ≥0∞) := by
  rw [rootMeasure, ofRoots_mass, ← (IsAlgClosed.splits Q).natDegree_eq_card_roots]

theorem rootMeasure_real_mass (Q : ℂ[X]) : (rootMeasure Q).real univ = Q.natDegree := by
  simp only [Measure.real, rootMeasure_mass, ENNReal.toReal_natCast]

@[simp] theorem rootMeasure_zero : rootMeasure 0 = 0 := by
  simp [rootMeasure]

@[simp] theorem rootMeasure_C (a : ℂ) : rootMeasure (Polynomial.C a) = 0 := by
  simp [rootMeasure]

theorem integrable_log_norm_ofRoots (r : Multiset ℂ) (w : ℂ) (hw : 0 ≤ w.im) :
    Integrable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) (ofRoots r) := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons ζ r ih =>
    rw [ofRoots_cons]
    exact (CayleyRootPotential.integrable_log_norm ζ.re |ζ.im| w (abs_nonneg _) hw).add_measure ih

theorem integrable_log_norm (Q : ℂ[X]) (w : ℂ) (hw : 0 ≤ w.im) :
    Integrable (fun t : ℝ => Real.log ‖w - (t : ℂ)‖) (rootMeasure Q) :=
  integrable_log_norm_ofRoots Q.roots w hw

theorem integrable_log_one_add_abs_ofRoots (r : Multiset ℂ) :
    Integrable (fun t : ℝ => Real.log (1 + |t|)) (ofRoots r) := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons ζ r ih =>
    rw [ofRoots_cons]
    exact (CayleyLogMoment.integrable_log_one_add_abs ζ.re |ζ.im| (abs_nonneg _)).add_measure ih

theorem integrable_log_one_add_abs (Q : ℂ[X]) :
    Integrable (fun t : ℝ => Real.log (1 + |t|)) (rootMeasure Q) :=
  integrable_log_one_add_abs_ofRoots Q.roots

theorem integral_log_norm_ofRoots (r : Multiset ℂ) (w : ℂ) (hw : 0 ≤ w.im) :
    (∫ t, Real.log ‖w - (t : ℂ)‖ ∂ofRoots r) =
      (r.map (fun ζ => Real.log ‖w - (ζ.re : ℂ) + ((|ζ.im| : ℝ) : ℂ) * Complex.I‖)).sum := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons ζ r ih =>
    simp only [ofRoots_cons, Multiset.map_cons, Multiset.sum_cons]
    rw [integral_add_measure
      (CayleyRootPotential.integrable_log_norm ζ.re |ζ.im| w (abs_nonneg _) hw)
      (integrable_log_norm_ofRoots r w hw),
      CayleyRootPotential.integral_log_norm ζ.re |ζ.im| w (abs_nonneg _) hw, ih]

def potential (Q : ℂ[X]) (w : ℂ) : ℝ :=
  ∫ t, Real.log ‖w - (t : ℂ)‖ ∂rootMeasure Q

theorem potential_eq_roots (Q : ℂ[X]) (w : ℂ) (hw : 0 ≤ w.im) :
    potential Q w =
      (Q.roots.map (fun ζ => Real.log ‖w - (ζ.re : ℂ) + ((|ζ.im| : ℝ) : ℂ) * Complex.I‖)).sum :=
  integral_log_norm_ofRoots Q.roots w hw

theorem reflected_norm_real (ζ : ℂ) (x : ℝ) :
    ‖(x : ℂ) - (ζ.re : ℂ) + ((|ζ.im| : ℝ) : ℂ) * Complex.I‖ = ‖(x : ℂ) - ζ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [sq_abs ζ.im]

theorem reflected_norm_ge (ζ w : ℂ) (hw : 0 ≤ w.im) :
    ‖w - ζ‖ ≤ ‖w - (ζ.re : ℂ) + ((|ζ.im| : ℝ) : ℂ) * Complex.I‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hp : 0 ≤ w.im * (|ζ.im| + ζ.im) :=
    mul_nonneg hw (by linarith [neg_abs_le ζ.im])
  nlinarith [sq_abs ζ.im]

theorem sub_root_ne_zero (Q : ℂ[X]) (w : ℂ) (hw : Q.eval w ≠ 0)
    (ζ : ℂ) (hζ : ζ ∈ Q.roots) : w - ζ ≠ 0 := by
  intro h
  have he : w = ζ := sub_eq_zero.mp h
  apply hw
  rw [he]
  exact Polynomial.isRoot_of_mem_roots hζ

private theorem norm_root_product (r : Multiset ℂ) (w : ℂ) :
    ‖(r.map (fun ζ => w - ζ)).prod‖ = (r.map (fun ζ => ‖w - ζ‖)).prod := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons ζ r ih => simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]

/-- The full product identity retains the leading coefficient and excludes
every actual zero factor via the nonzero evaluation hypothesis. -/
theorem log_eval_eq_roots (Q : ℂ[X]) (hQ : Q ≠ 0) (w : ℂ) (hw : Q.eval w ≠ 0) :
    Real.log ‖Q.eval w‖ = Real.log ‖Q.leadingCoeff‖ +
      (Q.roots.map (fun ζ => Real.log ‖w - ζ‖)).sum := by
  have he := (IsAlgClosed.splits Q).eval_eq_prod_roots w
  have hl : ‖Q.leadingCoeff‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hp : ‖(Q.roots.map (fun ζ => w - ζ)).prod‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro hz
    exact hw (by rw [he, hz, mul_zero])
  have hm : ∀ v ∈ Q.roots.map (fun ζ => ‖w - ζ‖), v ≠ 0 := by
    intro v hv
    obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hv
    exact norm_ne_zero_iff.mpr (sub_root_ne_zero Q w hw ζ hζ)
  calc
    _ = Real.log ‖Q.leadingCoeff‖ + Real.log ‖(Q.roots.map (fun ζ => w - ζ)).prod‖ := by
      rw [he, norm_mul, Real.log_mul hl hp]
    _ = _ := by
      simp only [norm_root_product, Real.log_multiset_prod hm, Multiset.map_map,
        Function.comp_def]

theorem boundary_eq (Q : ℂ[X]) (hQ : Q ≠ 0) (x : ℝ) (hx : Q.eval (x : ℂ) ≠ 0) :
    Real.log ‖Q.eval (x : ℂ)‖ = Real.log ‖Q.leadingCoeff‖ + potential Q (x : ℂ) := by
  rw [log_eval_eq_roots Q hQ (x : ℂ) hx, potential_eq_roots Q (x : ℂ) (by simp)]
  congr 1
  apply congrArg Multiset.sum
  exact Multiset.map_congr rfl (fun ζ _ => congrArg Real.log (reflected_norm_real ζ x).symm)

theorem upper_le (Q : ℂ[X]) (hQ : Q ≠ 0) (w : ℂ)
    (hw : 0 ≤ w.im) (hne : Q.eval w ≠ 0) :
    Real.log ‖Q.eval w‖ ≤ Real.log ‖Q.leadingCoeff‖ + potential Q w := by
  rw [log_eval_eq_roots Q hQ w hne, potential_eq_roots Q w hw]
  apply add_le_add le_rfl
  exact Multiset.sum_map_le_sum_map _ _ (fun ζ hζ =>
    Real.log_le_log (norm_pos_iff.mpr (sub_root_ne_zero Q w hne ζ hζ))
      (reflected_norm_ge ζ w hw))

/-- The real zero set is finite, even for complex coefficients. -/
theorem ae_eval_ne_zero (Q : ℂ[X]) (hQ : Q ≠ 0) :
    ∀ᵐ x : ℝ ∂volume, Q.eval (x : ℂ) ≠ 0 := by
  have hf : Set.Finite {x : ℝ | Q.eval (x : ℂ) = 0} :=
    (Polynomial.finite_setOfPred_isRoot hQ).preimage Complex.ofReal_injective.injOn
  exact hf.countable.ae_notMem volume

theorem boundary_eq_ae (Q : ℂ[X]) (hQ : Q ≠ 0) :
    ∀ᵐ x : ℝ ∂volume,
      Real.log ‖Q.eval (x : ℂ)‖ = Real.log ‖Q.leadingCoeff‖ + potential Q (x : ℂ) := by
  filter_upwards [ae_eval_ne_zero Q hQ] with x hx
  exact boundary_eq Q hQ x hx

end Jig133.PolynomialRootMeasure

end
end File_PolynomialRootMeasure

section File_FullRootSlopeWeak

/-!
# The actual full-polynomial logarithmic slope has a weak bound

Every complex root occurrence contributes its positive root measure. The
softened transform is computed and tends to the actual complex reciprocal sum.
No principal value identity, weak-slope oracle or real-root restriction is used.
-/

noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology ENNReal BigOperators
namespace Jig133.FullRootSlopeWeak
open SoftCauchyKernel FullProductLocalBand

theorem ofRoots_transform (r : Multiset ℂ) (h x : ℝ) (hh : 0 < h) :
    (∫ t, kernel h x t ∂PolynomialRootMeasure.ofRoots r) =
      (r.map (fun z => kernel (h + |z.im|) x z.re)).sum := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons z r ih =>
    rw [PolynomialRootMeasure.ofRoots_cons,
      integral_add_measure (integrable_kernel _ h x hh) (integrable_kernel _ h x hh),
      CayleySoftTransform.integral_kernel z.re |z.im| h x (abs_nonneg _) hh, ih]
    simp only [Multiset.map_cons, Multiset.sum_cons]

theorem transform_eq_sum (P : ℝ[X]) (h x : ℝ) (hh : 0 < h) :
    FiniteSoftCauchy.transform (PolynomialRootMeasure.rootMeasure (P.map Complex.ofRealHom)) h x =
      ∑ i : RootIndex P, kernel (h + |(root P i).im|) x (root P i).re := by
  rw [FiniteSoftCauchy.transform, PolynomialRootMeasure.rootMeasure, ofRoots_transform _ h x hh]
  exact (sum_roots P (fun z => kernel (h + |z.im|) x z.re)).symm

theorem reciprocal_re (z : ℂ) (x : ℝ) :
    (((x : ℂ) - z)⁻¹).re = (x - z.re) / ((x - z.re) ^ 2 + z.im ^ 2) := by
  rw [Complex.inv_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_apply]
  congr 1
  ring

theorem single_limit (z : ℂ) (x : ℝ) :
    Tendsto (fun h : ℝ => kernel (h + |z.im|) x z.re) (𝓝 0)
      (𝓝 ((((x : ℂ) - z)⁻¹).re)) := by
  rw [reciprocal_re]
  by_cases hx : x - z.re = 0
  · simpa only [kernel, hx, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _h : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  · have hn : (x - z.re) ^ 2 + (0 + |z.im|) ^ 2 ≠ 0 := by
      have hp := sq_pos_of_ne_zero hx
      positivity
    have hc : ContinuousAt (fun h : ℝ => (x - z.re) /
        ((x - z.re) ^ 2 + (h + |z.im|) ^ 2)) 0 :=
      continuousAt_const.div (continuousAt_const.add ((continuousAt_id.add_const _).pow 2)) hn
    simpa only [kernel, zero_add, sq_abs] using hc.tendsto

theorem transform_limit (P : ℝ[X]) (x : ℝ) :
    Tendsto (fun n : ℕ => FiniteSoftCauchy.transform
      (PolynomialRootMeasure.rootMeasure (P.map Complex.ofRealHom)) (1 / ((n : ℝ) + 1)) x)
      atTop (𝓝 (ComplexRootStability.slope (root P) x)) := by
  have hs := tendsto_finsetSum (Finset.univ : Finset (RootIndex P))
    (fun i _ => (single_limit (root P i) x).comp tendsto_one_div_add_atTop_nhds_zero_nat)
  apply hs.congr'
  exact Eventually.of_forall (fun n => (transform_eq_sum P (1 / ((n : ℝ) + 1)) x (by positivity)).symm)

theorem slope_set_subset (P : ℝ[X]) (L : ℝ) :
    {x : ℝ | L < |ComplexRootStability.slope (root P) x|} ⊆
      FiniteSoftCauchy.maximalSet (PolynomialRootMeasure.rootMeasure (P.map Complex.ofRealHom)) L := by
  intro x hx
  have he := ((continuous_abs.tendsto _).comp (transform_limit P x)).eventually (Ioi_mem_nhds hx)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

theorem log_derivative_bound (P : ℝ[X]) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | L < |P.derivative.eval x / P.eval x|} ≤
      ENNReal.ofReal (396 * (P.natDegree : ℝ) / L) := by
  have hsub : {x : ℝ | L < |P.derivative.eval x / P.eval x|} ⊆
      {x : ℝ | L < |ComplexRootStability.slope (root P) x|} := by
    intro x hx
    change L < |P.derivative.eval x / P.eval x| at hx
    change L < |ComplexRootStability.slope (root P) x|
    have hne : P.eval x ≠ 0 := by
      intro hz
      simp only [hz, div_zero, abs_zero] at hx
      exact (not_lt_of_ge hL.le) hx
    simpa only [log_derivative_eq_slope P hne] using hx
  have hb := FiniteSoftCauchy.maximal_bound
    (PolynomialRootMeasure.rootMeasure (P.map Complex.ofRealHom)) L hL
  rw [PolynomialRootMeasure.rootMeasure_real_mass,
    Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective] at hb
  exact (measure_mono (hsub.trans (slope_set_subset P L))).trans hb

theorem scaled_bound (P : ℝ[X]) (n : ℕ) (hn : 0 < n)
    (hdeg : P.natDegree ≤ 2 * n) (L : ℝ) (hL : 0 < L) :
    volume {x : ℝ | L * n < |P.derivative.eval x / P.eval x|} ≤ ENNReal.ofReal (792 / L) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (P.natDegree : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hdeg
  apply (log_derivative_bound P (L * n) (by positivity)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    396 * (P.natDegree : ℝ) / (L * n) ≤ 396 * (2 * (n : ℝ)) / (L * n) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (by positivity)
    _ = 792 / L := by
      field_simp
      norm_num

end Jig133.FullRootSlopeWeak

end
end File_FullRootSlopeWeak

section File_FullProductRootFilter

/-!
# A measurable exceptional set supplying actual full-product local control

The exceptional measure is uniform in coefficients and includes every root.
No good-center slope or projected-density premise remains after exclusion.
-/

noncomputable section
open Set MeasureTheory Polynomial
open scoped ENNReal
namespace Jig133.FullProductRootFilter
open FullProductLocalBand FullProductBandScale

theorem densitySet_open {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (A : ℝ) (hA : 0 < A) : IsOpen (FiniteRootDensity.densitySet z A) := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  obtain ⟨r, hr, hv⟩ := hx
  let d : ℝ := ((FiniteRootDensity.count z x r : ℝ) - A * r) / (2 * A)
  have hd : 0 < d := div_pos (sub_pos.mpr hv) (by positivity)
  have he : 2 * A * d = (FiniteRootDensity.count z x r : ℝ) - A * r := by
    dsimp [d]
    field_simp
  refine ⟨d, hd, ?_⟩
  intro y hy
  have hnear : |y - x| ≤ d := by
    exact (show |y - x| < d by simpa only [Metric.mem_ball, Real.dist_eq] using hy).le
  have hc : (FiniteRootDensity.count z x r : ℝ) ≤ FiniteRootDensity.count z y (r + d) := by
    exact_mod_cast FiniteRootDensity.count_le_shifted z x y r d hnear
  exact ⟨r + d, by positivity, by nlinarith⟩

def bad (P : ℝ[X]) (c B L : ℝ) (n : ℕ) : Set ℝ :=
  FullProductProjectedFilter.bad P c B n ∪ {x | L * n < |P.derivative.eval x / P.eval x|}

theorem measurableSet_bad (P : ℝ[X]) (c B L : ℝ) (n : ℕ)
    (hB : 0 < B) (hn : 0 < n) : MeasurableSet (bad P c B L n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply MeasurableSet.union
  · apply MeasurableSet.union
    · exact (densitySet_open (FullProductProjectedFilter.projected P) (2 * B * n) (by positivity)).measurableSet
    · exact MeasurableSet.iUnion (fun _ => measurableSet_Icc)
  · exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (P.derivative.continuous.measurable.div P.continuous.measurable))

theorem bad_volume_le (P : ℝ[X]) (c B L : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n) (hdeg : P.natDegree ≤ 2 * n) :
    volume (bad P c B L n) ≤ ENNReal.ofReal (6 / B + 4 * c + 792 / L) := by
  calc
    _ ≤ volume (FullProductProjectedFilter.bad P c B n) +
        volume {x : ℝ | L * n < |P.derivative.eval x / P.eval x|} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (6 / B + 4 * c) + ENNReal.ofReal (792 / L) :=
      add_le_add (FullProductProjectedFilter.bad_volume_le P c B n hc hB hn hdeg)
        (FullRootSlopeWeak.scaled_bound P n hn hdeg L hL)
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

theorem local_control (P : ℝ[X]) (hP : P ≠ 0) (c B L q : ℝ) (n : ℕ)
    (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n)
    (hq : q ∉ bad P c B L n) (x : ℝ) (hx : |x - q| ≤ width c B L / n) :
    P.eval x ≠ 0 ∧ (∀ i, (c - width c B L) / n ≤ |x - (root P i).re|) ∧
      |Real.log (|P.eval x|) - Real.log (|P.eval q|)| ≤ 1 / 2 := by
  have hg := FullProductProjectedFilter.controls_of_not_mem P c B q n
    (fun h => hq (Or.inl h))
  have hs : |P.derivative.eval q / P.eval q| ≤ L * n :=
    le_of_not_gt (fun h => hq (Or.inr h))
  exact local_log_bound P hP n hn q c B L hc hB hL hg.1 hg.2 hs x hx

theorem local_band (P : ℝ[X]) (hP : P ≠ 0) (c B L q η T A : ℝ) (n : ℕ)
    (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n)
    (hq : q ∉ bad P c B L n) (hband : η * A ≤ |P.eval q| ∧ |P.eval q| ≤ T * A)
    (x : ℝ) (hx : |x - q| ≤ width c B L / n) :
    (η * Real.exp (-(1 / 2 : ℝ))) * A ≤ |P.eval x| ∧
      |P.eval x| ≤ (T * Real.exp (1 / 2 : ℝ)) * A := by
  have ha := (width_bounds hc hB hL).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 := (local_control P hP c B L q n hc hB hL hn hq q (by simp; positivity)).1
  have hxc := local_control P hP c B L q n hc hB hL hn hq x hx
  exact band_from_log_bound P hq0 hxc.1 hband hxc.2.2

end Jig133.FullProductRootFilter

end
end File_FullProductRootFilter

section File_FiniteSourceNets

open Set
open scoped BigOperators

namespace Jig133.FiniteSourceNets

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Separation is measured on the actual finite real source set. -/
def Separated (Y : Finset ℝ) (ρ : ℝ) : Prop :=
  ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ρ ≤ |x - y|

/-- A finite maximal source net includes a strict covering radius. -/
def IsSourceNet (X Y : Finset ℝ) (ρ : ℝ) : Prop :=
  Y ⊆ X ∧ Separated Y ρ ∧ ∀ x ∈ X, ∃ y ∈ Y, |x - y| < ρ

/-- Every finite original row has such a net, including the empty row.
The proof maximizes cardinality inside its finite powerset. -/
theorem exists_sourceNet (X : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Y, IsSourceNet X Y ρ := by
  classical
  let candidates := X.powerset.filter (fun Y => Separated Y ρ)
  have hc : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset X, ?_⟩⟩
    intro x hx
    exact False.elim (Finset.notMem_empty x hx)
  obtain ⟨Y, hY, hmax⟩ := candidates.exists_max_image Finset.card hc
  obtain ⟨hYX, hsep⟩ := Finset.mem_filter.mp hY
  refine ⟨Y, Finset.mem_powerset.mp hYX, hsep, ?_⟩
  intro x hx
  by_contra hcover
  have hfar : ∀ y ∈ Y, ρ ≤ |x - y| := by
    intro y hy
    exact le_of_not_gt (fun h => hcover ⟨y, hy, h⟩)
  have hxY : x ∉ Y := by
    intro hy
    have := hfar x hy
    simp only [sub_self, abs_zero] at this
    linarith
  have hins : insert x Y ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx
      (Finset.mem_powerset.mp hYX)), ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | haY
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbY
      · exact False.elim (hab hbx.symm)
      · exact hfar b hbY
    · rcases Finset.mem_insert.mp hb with hbx | hbY
      · subst b
        simpa only [abs_sub_comm] using hfar a haY
      · exact hsep a haY b hbY hab
  have hcard := hmax (insert x Y) hins
  rw [Finset.card_insert_of_notMem hxY] at hcard
  omega

/-- Any subset retaining every separated point cannot properly enlarge a net. -/
theorem sourceNet_inclusion_maximal {X Y Z : Finset ℝ} {ρ : ℝ}
    (hY : IsSourceNet X Y ρ) (hYZ : Y ⊆ Z) (hZX : Z ⊆ X)
    (hZ : Separated Z ρ) : Z = Y := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxY
    obtain ⟨y, hy, hclose⟩ := hY.2.2 x (hZX hx)
    have hne : x ≠ y := by intro h; exact hxY (h ▸ hy)
    exact (not_lt_of_ge (hZ x hx y (hYZ hy) hne)) hclose
  · exact hYZ

/-- A half-open interval of exactly one separation length contains at most one source. -/
theorem card_filter_Ico_le_one {Y : Finset ℝ} {ρ : ℝ}
    (hsep : Separated Y ρ) (a : ℝ) :
    (Y.filter (fun x => x ∈ Ico a (a + ρ))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxY, hxa, hxb⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyY, hya, hyb⟩ := Finset.mem_filter.mp hy
  by_contra hne
  have h := hsep x hxY y hyY hne
  have : |x - y| < ρ := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact not_lt_of_ge h this

/-- The two closed endpoints account for the bound two rather than one. -/
theorem card_filter_Icc_le_two {Y : Finset ℝ} {ρ : ℝ}
    (hsep : Separated Y ρ) (a : ℝ) :
    (Y.filter (fun x => x ∈ Icc a (a + ρ))).card ≤ 2 := by
  classical
  let A := Y.filter (fun x => x ∈ Ico a (a + ρ))
  let B := Y.filter (fun x => x = a + ρ)
  have hsub : Y.filter (fun x => x ∈ Icc a (a + ρ)) ⊆ A ∪ B := by
    intro x hx
    obtain ⟨hxY, hxa, hxb⟩ := Finset.mem_filter.mp hx
    rcases lt_or_eq_of_le hxb with hlt | heq
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxY, hxa, hlt⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxY, heq⟩)
  have hA : A.card ≤ 1 := card_filter_Ico_le_one hsep a
  have hB : B.card ≤ 1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  omega

/-- A supplied interval representation, without disjointness or a minimality requirement. -/
def window {D : ℕ} (a b : Fin D → ℝ) : Set ℝ := ⋃ i, Icc (a i) (b i)

/-- Filtered membership in a finite interval union costs at most the sum of its counts. -/
theorem card_filter_window_le_sum {D : ℕ} (Y : Finset ℝ) (a b : Fin D → ℝ) :
    (Y.filter (fun x => x ∈ window a b)).card ≤
      ∑ i, (Y.filter (fun x => x ∈ Icc (a i) (b i))).card := by
  classical
  have heq : Y.filter (fun x => x ∈ window a b) =
      Finset.univ.biUnion (fun i => Y.filter (fun x => x ∈ Icc (a i) (b i))) := by
    ext x
    simp only [Finset.mem_filter, window, mem_iUnion, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    aesop
  rw [heq]
  exact Finset.card_biUnion_le

/-- Expanding every represented interval by one separation length adds at most
four sources per interval. Overlaps, degenerate intervals and D=0 are included. -/
theorem card_filter_expanded_window_le {D : ℕ} {Y : Finset ℝ} {ρ : ℝ}
    (hsep : Separated Y ρ) (a b : Fin D → ℝ) :
    (Y.filter (fun x => x ∈ window (fun i => a i - ρ) (fun i => b i + ρ))).card ≤
      (Y.filter (fun x => x ∈ window a b)).card + 4 * D := by
  classical
  let A := Y.filter (fun x => x ∈ window a b)
  let L := Y.filter (fun x => x ∈ window (fun i => a i - ρ) a)
  let R := Y.filter (fun x => x ∈ window b (fun i => b i + ρ))
  have hsub : Y.filter (fun x => x ∈ window (fun i => a i - ρ) (fun i => b i + ρ))
      ⊆ (A ∪ L) ∪ R := by
    intro x hx
    obtain ⟨hxY, hxw⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxw
    by_cases hl : x < a i
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hxY, mem_iUnion.mpr ⟨i, hi.1, hl.le⟩⟩))
    by_cases hr : b i < x
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hxY, mem_iUnion.mpr ⟨i, hr.le, hi.2⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hxY, mem_iUnion.mpr
          ⟨i, le_of_not_gt hl, le_of_not_gt hr⟩⟩))
  have hL : L.card ≤ 2 * D := by
    apply (card_filter_window_le_sum Y (fun i => a i - ρ) a).trans
    calc
      _ ≤ ∑ _i : Fin D, 2 := Finset.sum_le_sum (fun i _ => by
        have h := card_filter_Icc_le_two hsep (a i - ρ)
        simpa only [sub_add_cancel] using h)
      _ = 2 * D := by simp [Nat.mul_comm]
  have hR : R.card ≤ 2 * D := by
    apply (card_filter_window_le_sum Y b (fun i => b i + ρ)).trans
    calc
      _ ≤ ∑ _i : Fin D, 2 := Finset.sum_le_sum
        (fun i _ => card_filter_Icc_le_two hsep (b i))
      _ = 2 * D := by simp [Nat.mul_comm]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le (A ∪ L) R)
  have hAL := Finset.card_union_le A L
  change _ ≤ A.card + 4 * D
  omega

/-- The represented expansion is the actual closed distance enlargement.
The existential definition also treats the empty union correctly. -/
theorem mem_expanded_window_iff {D : ℕ} (a b : Fin D → ℝ)
    (hab : ∀ i, a i ≤ b i) {ρ : ℝ} (hρ : 0 ≤ ρ) (x : ℝ) :
    x ∈ window (fun i => a i - ρ) (fun i => b i + ρ) ↔
      ∃ z ∈ window a b, |x - z| ≤ ρ := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hl : x < a i
    · refine ⟨a i, mem_iUnion.mpr ⟨i, le_rfl, hab i⟩, ?_⟩
      exact abs_le.mpr ⟨by linarith [hi.1], by linarith⟩
    by_cases hr : b i < x
    · refine ⟨b i, mem_iUnion.mpr ⟨i, hab i, le_rfl⟩, ?_⟩
      exact abs_le.mpr ⟨by linarith, by linarith [hi.2]⟩
    · exact ⟨x, mem_iUnion.mpr ⟨i, le_of_not_gt hl, le_of_not_gt hr⟩,
        by simpa only [sub_self, abs_zero] using hρ⟩
  · rintro ⟨z, hz, hclose⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨hlo, hhi⟩ := abs_le.mp hclose
    exact mem_iUnion.mpr ⟨i, by linarith [hi.1], by linarith [hi.2]⟩

/-- Expanded-window net points cover EVERY original row point in the window;
no original root is discarded in passing to a maximal net. -/
theorem sourceNet_window_cover {D : ℕ} {X Y : Finset ℝ} {ρ : ℝ}
    (hnet : IsSourceNet X Y ρ) (a b : Fin D → ℝ) :
    ∀ x ∈ X, x ∈ window a b →
      ∃ y ∈ Y.filter (fun y => y ∈
        window (fun i => a i - ρ) (fun i => b i + ρ)), |x - y| < ρ := by
  intro x hx hxw
  obtain ⟨y, hy, hclose⟩ := hnet.2.2 x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxw
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hclose
  refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, hclose⟩
  exact mem_iUnion.mpr ⟨i, by linarith [hi.1], by linarith [hi.2]⟩


end
end Jig133.FiniteSourceNets
end File_FiniteSourceNets

section File_FiniteSourceGaps

/-!
# The actual finite source gaps, including both endpoint gaps

Adjoin -1 and 1 to the finite source set, sort it, and use consecutive
vertices. Original sources may already include either endpoint.
-/

noncomputable section
open Set
open scoped BigOperators
namespace Jig133.FiniteSourceGaps
attribute [local instance] Classical.propDecidable

abbrev I := Icc (-1 : ℝ) 1

def vertices (Y : Finset ℝ) : Finset ℝ := insert (-1) (insert 1 Y)
def count (Y : Finset ℝ) : ℕ := (vertices Y).card - 1

theorem vertices_nonempty (Y : Finset ℝ) : (vertices Y).Nonempty :=
  ⟨-1, Finset.mem_insert_self _ _⟩

def point (Y : Finset ℝ) : Fin (count Y + 1) ↪o ℝ :=
  (vertices Y).orderEmbOfFin (Nat.sub_add_cancel
    (Finset.card_pos.mpr (vertices_nonempty Y))).symm

def left (Y : Finset ℝ) (i : Fin (count Y)) : ℝ := point Y i.castSucc
def right (Y : Finset ℝ) (i : Fin (count Y)) : ℝ := point Y i.succ

theorem range_point (Y : Finset ℝ) : range (point Y) = (vertices Y : Set ℝ) :=
  Finset.range_orderEmbOfFin _ _

theorem point_mem (Y : Finset ℝ) (i : Fin (count Y + 1)) : point Y i ∈ vertices Y :=
  Finset.orderEmbOfFin_mem _ _ _

theorem point_in_interval {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ I)
    (i : Fin (count Y + 1)) : point Y i ∈ I := by
  have hm := point_mem Y i
  rcases Finset.mem_insert.mp hm with hm | hm
  · rw [hm]; constructor <;> norm_num
  · rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; constructor <;> norm_num
    · exact hY _ hm

theorem point_zero {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ I) : point Y 0 = -1 := by
  have hm : (-1 : ℝ) ∈ range (point Y) := by
    rw [range_point]; exact Finset.mem_insert_self _ _
  obtain ⟨j, hj⟩ := hm
  apply le_antisymm
  · rw [← hj]
    exact (point Y).monotone (Fin.zero_le j)
  · exact (point_in_interval hY 0).1

theorem point_last {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ I) :
    point Y (Fin.last (count Y)) = 1 := by
  have hm : (1 : ℝ) ∈ range (point Y) := by
    rw [range_point]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  obtain ⟨j, hj⟩ := hm
  apply le_antisymm
  · exact (point_in_interval hY _).2
  · rw [← hj]
    exact (point Y).monotone j.le_last

theorem gap_pos (Y : Finset ℝ) (i : Fin (count Y)) : left Y i < right Y i :=
  (point Y).strictMono i.castSucc_lt_succ

theorem gap_in_interval {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ I)
    (i : Fin (count Y)) : Icc (left Y i) (right Y i) ⊆ I := by
  intro x hx
  exact ⟨(point_in_interval hY i.castSucc).1.trans hx.1,
    hx.2.trans (point_in_interval hY i.succ).2⟩

theorem no_vertex_inside (Y : Finset ℝ) (i : Fin (count Y))
    {x : ℝ} (hx : x ∈ vertices Y) : x ∉ Ioo (left Y i) (right Y i) := by
  have hm : x ∈ range (point Y) := by rw [range_point]; exact hx
  obtain ⟨j, rfl⟩ := hm
  intro hg
  by_cases hj : j ≤ i.castSucc
  · exact (not_lt_of_ge ((point Y).monotone hj)) hg.1
  · have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hj)
    exact (not_lt_of_ge ((point Y).monotone hj')) hg.2

theorem source_at_gap_endpoint (Y : Finset ℝ) (i : Fin (count Y))
    {x : ℝ} (hx : x ∈ Y) (hg : x ∈ Icc (left Y i) (right Y i)) :
    x = left Y i ∨ x = right Y i := by
  have hnot := no_vertex_inside Y i
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
  by_cases hl : x = left Y i
  · exact Or.inl hl
  · right
    by_contra hr
    exact hnot ⟨lt_of_le_of_ne hg.1 (fun he => hl he.symm), lt_of_le_of_ne hg.2 hr⟩

theorem gap_source_count (Y : Finset ℝ) (i : Fin (count Y)) :
    (Y.filter (fun x => x ∈ Icc (left Y i) (right Y i))).card ≤ 2 := by
  have hs : Y.filter (fun x => x ∈ Icc (left Y i) (right Y i)) ⊆
      {left Y i, right Y i} := by
    intro x hx
    have h := Finset.mem_filter.mp hx
    rcases source_at_gap_endpoint Y i h.1 h.2 with h | h <;> simp [h]
  apply (Finset.card_le_card hs).trans
  simpa using Finset.card_insert_le (left Y i) {right Y i}

theorem gaps_cover {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ I) :
    (⋃ i, Ioo (left Y i) (right Y i)) = I \ (vertices Y : Set ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨gap_in_interval hY i ⟨hi.1.le, hi.2.le⟩,
      fun hv => no_vertex_inside Y i hv hi⟩
  · rintro ⟨hxI, hxV⟩
    have hne : ∀ i, x ≠ point Y i := by
      intro i he
      exact hxV (he ▸ point_mem Y i)
    rcases FiniteLevelGeometry.location_of_not_pole (point Y) hne with hl | hr | hg
    · rw [point_zero hY] at hl
      exact False.elim ((not_lt_of_ge hxI.1) hl)
    · rw [point_last hY] at hr
      exact False.elim ((not_lt_of_ge hxI.2) hr)
    · exact mem_iUnion.mpr hg

theorem sum_gap_lengths {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ I) :
    ∑ i : Fin (count Y), (right Y i - left Y i) = 2 := by
  have ha := Fin.sum_univ_succ (point Y : Fin (count Y + 1) → ℝ)
  have hb := Fin.sum_univ_castSucc (point Y : Fin (count Y + 1) → ℝ)
  rw [point_zero hY] at ha
  rw [point_last hY] at hb
  simp only [Finset.sum_sub_distrib, left, right]
  linarith only [ha, hb]

end Jig133.FiniteSourceGaps

end
end File_FiniteSourceGaps

section File_LongSourceGapBound

/-!
# Actual long-gap windows and their source/count budgets

Long gaps are selected from the actual sorted gap family. Their total
length bounds their count; at most two sources belong to each closed gap.
-/

noncomputable section
open Set
open scoped BigOperators
namespace Jig133.LongSourceGapBound
open FiniteSourceGaps FiniteSourceNets
attribute [local instance] Classical.propDecidable

def indices (Y : Finset ℝ) (H : ℝ) (n : ℕ) : Finset (Fin (count Y)) :=
  Finset.univ.filter (fun i => H / (n : ℝ) < right Y i - left Y i)

def gaps (Y : Finset ℝ) (H : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ indices Y H n, Icc (left Y i) (right Y i)

theorem gap_count_budget {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (H : ℝ) {n : ℕ} (hn : 0 < n) :
    ((indices Y H n).card : ℝ) * H ≤ 2 * n := by
  have hsum : ((indices Y H n).card : ℝ) * (H / n) ≤ 2 := by
    calc
      _ = ∑ _i ∈ indices Y H n, H / (n : ℝ) := by simp
      _ ≤ ∑ i ∈ indices Y H n, (right Y i - left Y i) :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
      _ ≤ ∑ i : Fin (count Y), (right Y i - left Y i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => (sub_pos.mpr (gap_pos Y i)).le)
      _ = 2 := sum_gap_lengths hY
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := mul_le_mul_of_nonneg_right hsum hn0.le
  simpa only [mul_assoc, div_mul_cancel₀ H hn0.ne'] using hh

theorem gaps_in_interval {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (H : ℝ) (n : ℕ) : gaps Y H n ⊆ Icc (-1 : ℝ) 1 := by
  intro x hx
  obtain ⟨i, hx⟩ := mem_iUnion.mp hx
  obtain ⟨_, hx⟩ := mem_iUnion.mp hx
  exact gap_in_interval hY i hx

/-- A literal enumeration gives the exact representation consumed by SC. -/
theorem exists_windows {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (H : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ D : ℕ, ∃ a b : Fin D → ℝ, (∀ i, a i ≤ b i) ∧
      window a b = gaps Y H n ∧
      (Y.filter (fun x => x ∈ window a b)).card ≤ 2 * D ∧
      (D : ℝ) * H ≤ 2 * n := by
  let T := indices Y H n
  let f : Fin T.card → T := T.equivFin.symm
  let a : Fin T.card → ℝ := fun i => left Y (f i)
  let b : Fin T.card → ℝ := fun i => right Y (f i)
  refine ⟨T.card, a, b, fun i => (gap_pos Y (f i)).le, ?_, ?_, gap_count_budget hY H hn⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨f i, mem_iUnion.mpr ⟨(f i).property, hi⟩⟩
    · intro hx
      obtain ⟨i, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hi, hx⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨T.equivFin ⟨i, hi⟩, ?_⟩
      simpa only [a, b, f, Equiv.symm_apply_apply] using hx
  · apply (card_filter_window_le_sum Y a b).trans
    calc
      _ ≤ ∑ _i : Fin T.card, 2 :=
        Finset.sum_le_sum (fun i _ => gap_source_count Y (f i))
      _ = 2 * T.card := by simp [Nat.mul_comm]

/-- Increasing the cutoff removes gaps, with no change to the source family. -/
theorem gaps_antitone (Y : Finset ℝ) {H H' : ℝ} (hH : H ≤ H') (n : ℕ) :
    gaps Y H' n ⊆ gaps Y H n := by
  intro x hx
  obtain ⟨i, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hi, hx⟩ := mem_iUnion.mp hx
  have hi' : i ∈ indices Y H n := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (div_le_div_of_nonneg_right hH (Nat.cast_nonneg n)).trans_lt
      (Finset.mem_filter.mp hi).2⟩
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi', hx⟩⟩

end Jig133.LongSourceGapBound

end
end File_LongSourceGapBound

section File_DiscreteRankDensity

/-!
# An actual discrete rank-span exceptional set

Each bad index belongs to a consecutive interval whose weight exceeds its
length times the threshold. Disjoint unit cells turn index count into measure.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Jig133.DiscreteRankDensity
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

def span (g : Fin m → ℝ) (a b : Fin m) : ℝ := ∑ j ∈ Finset.Icc a b, g j

def badIndices (g : Fin m → ℝ) (T : ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ a b : Fin m, a ≤ i ∧ i ≤ b ∧
    T * ((b.val + 1 - a.val : ℕ) : ℝ) < span g a b)

def cell (i : Fin m) : Set ℝ := Ioc ((i.val : ℝ) - 1 / 2) ((i.val : ℝ) + 1 / 2)

def cells (S : Finset (Fin m)) : Set ℝ := ⋃ i ∈ S, cell i

theorem cells_volume (S : Finset (Fin m)) : volume.real (cells S) = S.card := by
  have hd : Set.PairwiseDisjoint (↑S) (cell (m := m)) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro x ⟨hxi, hix⟩ ⟨hxj, hjx⟩
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hg : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
      linarith
    · have hg : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast (show j.val + 1 ≤ i.val by omega)
      linarith
  have hv (i : Fin m) : volume.real (cell i) = 1 := by
    rw [cell, Real.volume_real_Ioc_of_le (by linarith)]
    ring
  rw [cells, measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ioc)
    (fun _ _ => by simp [cell])]
  simp only [hv, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem span_le_ball (g : Fin m → ℝ) (hg : ∀ j, 0 ≤ g j)
    (a b i : Fin m) (hai : a ≤ i) (hib : i ≤ b) (x : ℝ) (hx : x ∈ cell i) :
    span g a b ≤ AtomicCauchyCotlar.ballMass (fun j : Fin m => (j.val : ℝ)) g x
      ((b.val + 1 - a.val : ℕ) : ℝ) := by
  have hr : ((b.val + 1 - a.val : ℕ) : ℝ) = (b.val : ℝ) + 1 - a.val := by
    rw [Nat.cast_sub (by have := hai.trans hib; exact Nat.le_succ_of_le this)]
    push_cast
    ring
  have hia : (a.val : ℝ) ≤ i.val := by exact_mod_cast hai
  have hibR : (i.val : ℝ) ≤ b.val := by exact_mod_cast hib
  have hbnd (j : Fin m) (hj : j ∈ Finset.Icc a b) :
      |x - (j.val : ℝ)| ≤ ((b.val + 1 - a.val : ℕ) : ℝ) := by
    have hjR := Finset.mem_Icc.mp hj
    have hja : (a.val : ℝ) ≤ j.val := by exact_mod_cast hjR.1
    have hjb : (j.val : ℝ) ≤ b.val := by exact_mod_cast hjR.2
    rw [hr, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  calc
    span g a b = ∑ j ∈ Finset.Icc a b,
        if |x - (j.val : ℝ)| ≤ ((b.val + 1 - a.val : ℕ) : ℝ) then g j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (if_pos (hbnd j hj)).symm
    _ ≤ AtomicCauchyCotlar.ballMass (fun j : Fin m => (j.val : ℝ)) g x
        ((b.val + 1 - a.val : ℕ) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      split_ifs
      · exact hg j
      · exact le_rfl

theorem bad_cells_subset (g : Fin m → ℝ) (hg : ∀ j, 0 ≤ g j) (T : ℝ) :
    cells (badIndices g T) ⊆ AtomicCauchyCotlar.densitySet
      (fun j : Fin m => (j.val : ℝ)) g (T / 2) := by
  intro x hx
  obtain ⟨i, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hi, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨a, b, hai, hib, hv⟩ := (Finset.mem_filter.mp hi).2
  have hab : a.val ≤ b.val := hai.trans hib
  refine ⟨((b.val + 1 - a.val : ℕ) : ℝ), by exact_mod_cast (show 0 < b.val + 1 - a.val by omega), ?_⟩
  have he := hv.trans_le (span_le_ball g hg a b i hai hib x hxi)
  calc
    _ = T * ((b.val + 1 - a.val : ℕ) : ℝ) := by ring
    _ < _ := he

theorem bad_card_le (g : Fin m → ℝ) (hg : ∀ j, 0 ≤ g j) (T : ℝ) (hT : 0 < T) :
    ((badIndices g T).card : ℝ) ≤ 6 * (∑ j, g j) / T := by
  have hb := (measure_mono (bad_cells_subset g hg T)).trans
    (AtomicCauchyCotlar.densitySet_volume_le (fun j : Fin m => (j.val : ℝ)) g hg
      (T / 2) (by positivity))
  have hmass : 0 ≤ ∑ j, g j := Finset.sum_nonneg (fun j _ => hg j)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  change volume.real (cells (badIndices g T)) ≤ _ at hr
  rw [cells_volume] at hr
  calc
    _ ≤ 3 * (∑ j, g j) / (T / 2) := hr
    _ = _ := by ring

theorem span_le_of_good (g : Fin m → ℝ) (T : ℝ) (i : Fin m)
    (hi : i ∉ badIndices g T) (a b : Fin m) (hai : a ≤ i) (hib : i ≤ b) :
    span g a b ≤ T * ((b.val + 1 - a.val : ℕ) : ℝ) := by
  apply le_of_not_gt
  intro h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, a, b, hai, hib, h⟩)

end Jig133.DiscreteRankDensity

end
end File_DiscreteRankDensity

section File_SourceRankGeometry

/-!
# Actual source-rank spans and the physical cost of bad short gaps

The sorted vertices include both endpoints. No upper gap assumption is used
for rank counting; physical deletion is charged only after filtering short gaps.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Jig133.SourceRankGeometry
open FiniteSourceGaps
attribute [local instance] Classical.propDecidable

def length (Y : Finset ℝ) (i : Fin (count Y)) : ℝ := right Y i - left Y i

def badIndices (Y : Finset ℝ) (C : ℝ) (n : ℕ) : Finset (Fin (count Y)) :=
  DiscreteRankDensity.badIndices (length Y) (C / n)

theorem span_eq (Y : Finset ℝ) (a b : Fin (count Y)) (hab : a ≤ b) :
    DiscreteRankDensity.span (length Y) a b = point Y b.succ - point Y a.castSucc := by
  exact Fin.sum_Icc_sub hab (point Y)

theorem bad_card_le {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (C : ℝ) (hC : 0 < C) (n : ℕ) (hn : 0 < n) :
    ((badIndices Y C n).card : ℝ) ≤ 12 * n / C := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := DiscreteRankDensity.bad_card_le (length Y)
    (fun i => (sub_pos.mpr (gap_pos Y i)).le) (C / n) (div_pos hC hnR)
  have hs : (∑ i, length Y i) = 2 := sum_gap_lengths hY
  rw [hs] at hb
  calc
    _ ≤ 6 * 2 / (C / n) := hb
    _ = _ := by field_simp; ring

theorem good_span (Y : Finset ℝ) (C : ℝ) (n : ℕ) (i : Fin (count Y))
    (hi : i ∉ badIndices Y C n) (a b : Fin (count Y)) (hai : a ≤ i) (hib : i ≤ b) :
    point Y b.succ - point Y a.castSucc ≤ C * ((b.val + 1 - a.val : ℕ) : ℝ) / n := by
  have hb := DiscreteRankDensity.span_le_of_good (length Y) (C / n) i hi a b hai hib
  rw [span_eq Y a b (hai.trans hib)] at hb
  calc
    _ ≤ (C / n) * ((b.val + 1 - a.val : ℕ) : ℝ) := hb
    _ = _ := by ring

theorem left_rank_distance (Y : Finset ℝ) (C : ℝ) (n : ℕ) (i a : Fin (count Y))
    (hi : i ∉ badIndices Y C n) (hai : a ≤ i) (x : ℝ) (hx : x ∈ Icc (left Y i) (right Y i)) :
    0 ≤ x - point Y a.castSucc ∧
      x - point Y a.castSucc ≤ C * ((i.val + 1 - a.val : ℕ) : ℝ) / n := by
  have hs := good_span Y C n i hi a i hai le_rfl
  have ho := (point Y).monotone (show a.castSucc ≤ i.castSucc from hai)
  change point Y i.succ - point Y a.castSucc ≤ _ at hs
  change point Y i.castSucc ≤ x ∧ x ≤ point Y i.succ at hx
  constructor <;> linarith

theorem right_rank_distance (Y : Finset ℝ) (C : ℝ) (n : ℕ) (i b : Fin (count Y))
    (hi : i ∉ badIndices Y C n) (hib : i ≤ b) (x : ℝ) (hx : x ∈ Icc (left Y i) (right Y i)) :
    0 ≤ point Y b.succ - x ∧
      point Y b.succ - x ≤ C * ((b.val + 1 - i.val : ℕ) : ℝ) / n := by
  have hs := good_span Y C n i hi i b le_rfl hib
  have ho := (point Y).monotone (show i.succ ≤ b.succ from Nat.succ_le_succ hib)
  change point Y i.castSucc ≤ x ∧ x ≤ point Y i.succ at hx
  constructor <;> linarith

def shortBad (Y : Finset ℝ) (C G : ℝ) (n : ℕ) : Finset (Fin (count Y)) :=
  (badIndices Y C n).filter (fun i => length Y i ≤ G / n)

def shortBadUnion (Y : Finset ℝ) (C G : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ shortBad Y C G n, Icc (left Y i) (right Y i)

theorem measurableSet_shortBadUnion (Y : Finset ℝ) (C G : ℝ) (n : ℕ) :
    MeasurableSet (shortBadUnion Y C G n) :=
  MeasurableSet.biUnion (shortBad Y C G n).countable_toSet (fun _ _ => measurableSet_Icc)

theorem shortBadUnion_volume_le {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (C G : ℝ) (hC : 0 < C) (hG : 0 ≤ G) (n : ℕ) (hn : 0 < n) :
    volume.real (shortBadUnion Y C G n) ≤ 12 * G / C := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg (i : Fin (count Y)) : volume.real (Icc (left Y i) (right Y i)) = length Y i :=
    Real.volume_real_Icc_of_le (gap_pos Y i).le
  have hcard : ((shortBad Y C G n).card : ℝ) ≤ (badIndices Y C n).card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun i => length Y i ≤ G / n) (badIndices Y C n))
  calc
    _ ≤ ∑ i ∈ shortBad Y C G n, volume.real (Icc (left Y i) (right Y i)) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ i ∈ shortBad Y C G n, length Y i := Finset.sum_congr rfl (fun i _ => hg i)
    _ ≤ ∑ _i ∈ shortBad Y C G n, G / (n : ℝ) :=
      Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ = ((shortBad Y C G n).card : ℝ) * (G / n) := by simp
    _ ≤ ((badIndices Y C n).card : ℝ) * (G / n) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hG hnR.le)
    _ ≤ (12 * n / C) * (G / n) :=
      mul_le_mul_of_nonneg_right (bad_card_le hY C hC n hn) (div_nonneg hG hnR.le)
    _ = _ := by field_simp

end Jig133.SourceRankGeometry

end
end File_SourceRankGeometry

section File_SourceGapSelection

/-!
# Finite selection of actual internal source gaps and anchors

One anchor is chosen in each qualifying gap. Cardinality and mass refer to
the actual finite selection; no measurable selection theorem is used.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Jig133.SourceGapSelection
open FiniteSourceGaps
attribute [local instance] Classical.propDecidable

def qualifies (Y : Finset ℝ) (Q : Set ℝ) (i : Fin (count Y)) : Prop :=
  left Y i ∈ Y ∧ right Y i ∈ Y ∧ (Q ∩ Ioo (left Y i) (right Y i)).Nonempty

def indices (Y : Finset ℝ) (Q : Set ℝ) : Finset (Fin (count Y)) :=
  Finset.univ.filter (qualifies Y Q)

def anchor (Y : Finset ℝ) (Q : Set ℝ) (i : Fin (count Y)) : ℝ :=
  if h : qualifies Y Q i then Classical.choose h.2.2 else 0

theorem anchor_mem (Y : Finset ℝ) (Q : Set ℝ) (i : Fin (count Y))
    (hi : i ∈ indices Y Q) : anchor Y Q i ∈ Q ∧ anchor Y Q i ∈ Ioo (left Y i) (right Y i) := by
  have h := (Finset.mem_filter.mp hi).2
  simp only [anchor, dif_pos h]
  exact Classical.choose_spec h.2.2

theorem card_le (Y : Finset ℝ) (Q : Set ℝ) : (indices Y Q).card ≤ Y.card := by
  apply Finset.card_le_card_of_injOn (left Y)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.1
  · intro i _ j _ he
    apply Fin.ext
    exact congrArg (fun k : Fin (count Y + 1) => k.val) ((point Y).injective he)

theorem cover (Y : Finset ℝ) (Q : Set ℝ)
    (hQ : ∀ q ∈ Q, ∃ i : Fin (count Y), left Y i ∈ Y ∧ right Y i ∈ Y ∧
      q ∈ Ioo (left Y i) (right Y i)) :
    Q ⊆ ⋃ i ∈ indices Y Q, Icc (left Y i) (right Y i) := by
  intro q hq
  obtain ⟨i, hl, hr, hgap⟩ := hQ q hq
  have hi : i ∈ indices Y Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hr, q, hq, hgap⟩
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hgap.1.le, hgap.2.le⟩⟩

theorem mass_le (Y : Finset ℝ) (Q : Set ℝ) (G : ℝ) (n : ℕ)
    (hQ : ∀ q ∈ Q, ∃ i : Fin (count Y), left Y i ∈ Y ∧ right Y i ∈ Y ∧
      q ∈ Ioo (left Y i) (right Y i))
    (hshort : ∀ i ∈ indices Y Q, right Y i - left Y i ≤ G / n) :
    volume.real Q ≤ ((indices Y Q).card : ℝ) * (G / n) := by
  have hf : volume (⋃ i ∈ indices Y Q, Icc (left Y i) (right Y i)) ≠ ⊤ :=
    measure_biUnion_ne_top (indices Y Q).finite_toSet (fun _ _ => by simp)
  calc
    _ ≤ volume.real (⋃ i ∈ indices Y Q, Icc (left Y i) (right Y i)) :=
      measureReal_mono (cover Y Q hQ) hf
    _ ≤ ∑ i ∈ indices Y Q, volume.real (Icc (left Y i) (right Y i)) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ i ∈ indices Y Q, (right Y i - left Y i) :=
      Finset.sum_congr rfl (fun i _ => Real.volume_real_Icc_of_le (gap_pos Y i).le)
    _ ≤ ∑ _i ∈ indices Y Q, G / (n : ℝ) := Finset.sum_le_sum (fun i hi => hshort i hi)
    _ = _ := by simp

theorem card_lower (Y : Finset ℝ) (Q : Set ℝ) (G δ : ℝ) (n : ℕ)
    (hG : 0 < G) (hn : 0 < n) (hδ : δ ≤ volume.real Q)
    (hQ : ∀ q ∈ Q, ∃ i : Fin (count Y), left Y i ∈ Y ∧ right Y i ∈ Y ∧
      q ∈ Ioo (left Y i) (right Y i))
    (hshort : ∀ i ∈ indices Y Q, right Y i - left Y i ≤ G / n) :
    δ * n / G ≤ (indices Y Q).card := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hG).mpr
  have hb := mul_le_mul_of_nonneg_right (hδ.trans (mass_le Y Q G n hQ hshort)) hnR.le
  simpa only [mul_assoc, div_mul_cancel₀ G hnR.ne'] using hb

theorem rank_good (Y : Finset ℝ) (Q : Set ℝ) (C G : ℝ) (n : ℕ)
    (hQ : ∀ q ∈ Q, q ∉ SourceRankGeometry.shortBadUnion Y C G n)
    (hshort : ∀ i ∈ indices Y Q, right Y i - left Y i ≤ G / n)
    (i : Fin (count Y)) (hi : i ∈ indices Y Q) : i ∉ SourceRankGeometry.badIndices Y C n := by
  intro hb
  have hq := anchor_mem Y Q i hi
  apply hQ (anchor Y Q i) hq.1
  refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hq.2.1.le, hq.2.2.le⟩⟩
  exact Finset.mem_filter.mpr ⟨hb, hshort i hi⟩

end Jig133.SourceGapSelection

end
end File_SourceGapSelection

section File_SourceGapSelectionCover

/-!
# Instantiating finite gap selection from the actual long-gap filter

Interior target points outside sources and long gaps lie in indexed internal
gaps. This supplies the selector's coverage and shortness, not just neighbors.
-/

noncomputable section
open Set MeasureTheory
namespace Jig133.SourceGapSelectionCover
open FiniteSourceGaps SourceGapSelection
attribute [local instance] Classical.propDecidable

theorem internal_index {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (G : ℝ) (n : ℕ) {ρ x : ℝ} (hρ : 0 ≤ ρ) (hscale : G / (n : ℝ) ≤ ρ)
    (hx : x ∈ Ioo (-1 + ρ) (1 - ρ)) (hxY : x ∉ Y)
    (hxG : x ∉ LongSourceGapBound.gaps Y G n) :
    ∃ i : Fin (count Y), left Y i ∈ Y ∧ right Y i ∈ Y ∧
      x ∈ Ioo (left Y i) (right Y i) ∧ right Y i - left Y i ≤ G / n := by
  have hxlo : -1 < x := by linarith [hx.1]
  have hxhi : x < 1 := by linarith [hx.2]
  have hxV : x ∉ vertices Y := by
    intro hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · linarith
    · rcases Finset.mem_insert.mp hm with hm | hm
      · linarith
      · exact hxY hm
  have hcover : x ∈ ⋃ i, Ioo (left Y i) (right Y i) := by
    rw [gaps_cover hY]
    exact ⟨⟨hxlo.le, hxhi.le⟩, hxV⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  have hlen : right Y i - left Y i ≤ G / n := by
    apply le_of_not_gt
    intro h
    exact hxG (mem_iUnion.mpr ⟨i, mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hi.1.le, hi.2.le⟩⟩)
  have ha : left Y i ∈ Y := by
    have hm := point_mem Y i.castSucc
    change left Y i ∈ vertices Y at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exfalso; nlinarith only [hm, hi.2, hx.1, hlen, hscale]
    · rcases Finset.mem_insert.mp hm with hm | hm
      · exfalso; linarith only [hm, hi.1, hxhi]
      · exact hm
  have hb : right Y i ∈ Y := by
    have hm := point_mem Y i.succ
    change right Y i ∈ vertices Y at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exfalso; linarith only [hm, hi.2, hxlo]
    · rcases Finset.mem_insert.mp hm with hm | hm
      · exfalso; nlinarith only [hm, hi.1, hx.2, hlen, hscale]
      · exact hm
  exact ⟨i, ha, hb, hi, hlen⟩

theorem all_short (Y : Finset ℝ) (Q : Set ℝ) (G : ℝ) (n : ℕ)
    (hQ : ∀ q ∈ Q, q ∉ LongSourceGapBound.gaps Y G n)
    (i : Fin (count Y)) (hi : i ∈ indices Y Q) : right Y i - left Y i ≤ G / n := by
  have hq := anchor_mem Y Q i hi
  apply le_of_not_gt
  intro hlong
  apply hQ (anchor Y Q i) hq.1
  refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hq.2.1.le, hq.2.2.le⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlong⟩

theorem actual_card_lower {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (Q : Set ℝ) (G δ ρ : ℝ) (n : ℕ) (hG : 0 < G) (hn : 0 < n)
    (hρ : 0 ≤ ρ) (hscale : G / (n : ℝ) ≤ ρ)
    (hQ : ∀ q ∈ Q, q ∈ Ioo (-1 + ρ) (1 - ρ))
    (hYavoid : ∀ q ∈ Q, q ∉ Y)
    (hGavoid : ∀ q ∈ Q, q ∉ LongSourceGapBound.gaps Y G n)
    (hδ : δ ≤ volume.real Q) : δ * n / G ≤ (indices Y Q).card := by
  apply card_lower Y Q G δ n hG hn hδ
  · intro q hq
    obtain ⟨i, hl, hr, hgap, _⟩ := internal_index hY G n hρ hscale
      (hQ q hq) (hYavoid q hq) (hGavoid q hq)
    exact ⟨i, hl, hr, hgap⟩
  · exact all_short Y Q G n hGavoid

theorem actual_rank_good (Y : Finset ℝ) (Q : Set ℝ) (C G : ℝ) (n : ℕ)
    (hGavoid : ∀ q ∈ Q, q ∉ LongSourceGapBound.gaps Y G n)
    (hRavoid : ∀ q ∈ Q, q ∉ SourceRankGeometry.shortBadUnion Y C G n)
    (i : Fin (count Y)) (hi : i ∈ indices Y Q) : i ∉ SourceRankGeometry.badIndices Y C n :=
  rank_good Y Q C G n hRavoid (all_short Y Q G n hGavoid) i hi

end Jig133.SourceGapSelectionCover

end
end File_SourceGapSelectionCover

section File_SourceGapWindows

/-!
# Actual disjoint windows in the selected source gaps

Full-product nonvanishing prevents a window from crossing a source endpoint.
This gives disjoint closed windows and exact total length, not an overlap loss.
-/

noncomputable section
open Set MeasureTheory Polynomial
namespace Jig133.SourceGapWindows
open FiniteSourceGaps SourceGapSelection FullProductBandScale
attribute [local instance] Classical.propDecidable

def window (Y : Finset ℝ) (Q : Set ℝ) (c B L : ℝ) (n : ℕ)
    (i : Fin (count Y)) : Set ℝ :=
  Icc (anchor Y Q i - width c B L / n) (anchor Y Q i + width c B L / n)

def windows (Y : Finset ℝ) (Q : Set ℝ) (c B L : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ indices Y Q, window Y Q c B L n i

theorem window_subset_gap (Y : Finset ℝ) (Q : Set ℝ) (P : ℝ[X]) (hP : P ≠ 0)
    (c B L : ℝ) (n : ℕ) (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n)
    (hroots : ∀ y ∈ Y, P.eval y = 0)
    (hQ : ∀ q ∈ Q, q ∉ FullProductRootFilter.bad P c B L n)
    (i : Fin (count Y)) (hi : i ∈ indices Y Q) :
    window Y Q c B L n i ⊆ Ioo (left Y i) (right Y i) := by
  have hq := anchor_mem Y Q i hi
  have hp := (Finset.mem_filter.mp hi).2
  have hzero (x : ℝ) (hx : |x - anchor Y Q i| ≤ width c B L / n) : P.eval x ≠ 0 :=
    (FullProductRootFilter.local_control P hP c B L (anchor Y Q i) n
      hc hB hL hn (hQ _ hq.1) x hx).1
  have hl : left Y i < anchor Y Q i - width c B L / n := by
    by_contra hh
    have hx : |left Y i - anchor Y Q i| ≤ width c B L / n := by
      rw [abs_le]; constructor <;> linarith [hq.2.1, not_lt.mp hh]
    exact hzero _ hx (hroots _ hp.1)
  have hr : anchor Y Q i + width c B L / n < right Y i := by
    by_contra hh
    have hx : |right Y i - anchor Y Q i| ≤ width c B L / n := by
      rw [abs_le]; constructor <;> linarith [hq.2.2, not_lt.mp hh]
    exact hzero _ hx (hroots _ hp.2.1)
  intro x hx
  exact ⟨hl.trans_le hx.1, hx.2.trans_lt hr⟩

theorem windows_disjoint (Y : Finset ℝ) (Q : Set ℝ) (P : ℝ[X]) (hP : P ≠ 0)
    (c B L : ℝ) (n : ℕ) (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n)
    (hroots : ∀ y ∈ Y, P.eval y = 0)
    (hQ : ∀ q ∈ Q, q ∉ FullProductRootFilter.bad P c B L n) :
    Set.PairwiseDisjoint (↑(indices Y Q)) (window Y Q c B L n) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi' := window_subset_gap Y Q P hP c B L n hc hB hL hn hroots hQ i hi hxi
  have hj' := window_subset_gap Y Q P hP c B L n hc hB hL hn hroots hQ j hj hxj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have ho : right Y i ≤ left Y j :=
      (point Y).monotone (show i.succ ≤ j.castSucc from Nat.succ_le_of_lt hlt)
    linarith [hi'.2, hj'.1]
  · have ho : right Y j ≤ left Y i :=
      (point Y).monotone (show j.succ ≤ i.castSucc from Nat.succ_le_of_lt hgt)
    linarith [hj'.2, hi'.1]

theorem windows_volume (Y : Finset ℝ) (Q : Set ℝ) (P : ℝ[X]) (hP : P ≠ 0)
    (c B L : ℝ) (n : ℕ) (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n)
    (hroots : ∀ y ∈ Y, P.eval y = 0)
    (hQ : ∀ q ∈ Q, q ∉ FullProductRootFilter.bad P c B L n) :
    volume.real (windows Y Q c B L n) = (indices Y Q).card * (2 * width c B L / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha := (width_bounds hc hB hL).1
  have hv (i : Fin (count Y)) : volume.real (window Y Q c B L n i) = 2 * width c B L / n := by
    rw [window, Real.volume_real_Icc_of_le (by have := div_pos ha hnR; linarith)]
    ring
  rw [windows, measureReal_biUnion_finset
    (windows_disjoint Y Q P hP c B L n hc hB hL hn hroots hQ)
    (fun _ _ => measurableSet_Icc) (fun _ _ => by simp [window])]
  simp only [hv, Finset.sum_const, nsmul_eq_mul]

theorem window_band (Y : Finset ℝ) (Q : Set ℝ) (P : ℝ[X]) (hP : P ≠ 0)
    (c B L η T A : ℝ) (n : ℕ) (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n)
    (hQ : ∀ q ∈ Q, q ∉ FullProductRootFilter.bad P c B L n)
    (hband : ∀ q ∈ Q, η * A ≤ |P.eval q| ∧ |P.eval q| ≤ T * A)
    (i : Fin (count Y)) (hi : i ∈ indices Y Q) (x : ℝ) (hx : x ∈ window Y Q c B L n i) :
    (η * Real.exp (-(1 / 2 : ℝ))) * A ≤ |P.eval x| ∧
      |P.eval x| ≤ (T * Real.exp (1 / 2 : ℝ)) * A := by
  have hq := (anchor_mem Y Q i hi).1
  apply FullProductRootFilter.local_band P hP c B L (anchor Y Q i) η T A n
    hc hB hL hn (hQ _ hq) (hband _ hq) x
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem actual_volume_lower {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (Q : Set ℝ) (P : ℝ[X]) (hP : P ≠ 0) (c B L G δ ρ : ℝ) (n : ℕ)
    (hc : 0 < c) (hB : 0 < B) (hL : 0 < L) (hG : 0 < G) (hn : 0 < n)
    (hρ : 0 ≤ ρ) (hscale : G / (n : ℝ) ≤ ρ)
    (hroots : ∀ y ∈ Y, P.eval y = 0)
    (hQ : ∀ q ∈ Q, q ∉ FullProductRootFilter.bad P c B L n)
    (hinterior : ∀ q ∈ Q, q ∈ Ioo (-1 + ρ) (1 - ρ))
    (hYavoid : ∀ q ∈ Q, q ∉ Y)
    (hGavoid : ∀ q ∈ Q, q ∉ LongSourceGapBound.gaps Y G n)
    (hδ : δ ≤ volume.real Q) :
    2 * width c B L * δ / G ≤ volume.real (windows Y Q c B L n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha := (width_bounds hc hB hL).1
  have hk := SourceGapSelectionCover.actual_card_lower hY Q G δ ρ n hG hn hρ hscale
    hinterior hYavoid hGavoid hδ
  rw [windows_volume Y Q P hP c B L n hc hB hL hn hroots hQ]
  calc
    _ = (δ * n / G) * (2 * width c B L / n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (by positivity)

end Jig133.SourceGapWindows

end
end File_SourceGapWindows

section File_BandTargetMeasure

/-!
# The actual retained band and its deletion budget

Long-gap loss is charged only inside the fixed target E. All other deletions
are the literal checked exceptional sets; their union determines Q.
-/

noncomputable section
open Set MeasureTheory Polynomial
open scoped ENNReal
namespace Jig133.BandTargetMeasure

def edge (ρ : ℝ) : Set ℝ := Icc (-1 : ℝ) 1 \ Ioo (-1 + ρ) (1 - ρ)

def band (P : ℝ[X]) (η T A : ℝ) : Set ℝ :=
  {x | η * A ≤ |P.eval x| ∧ |P.eval x| ≤ T * A}

def excluded (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (c B L C G ρ : ℝ) (n : ℕ) : Set ℝ :=
  (((edge ρ ∪ (E ∩ LongSourceGapBound.gaps Y G n)) ∪
    SourceRankGeometry.shortBadUnion Y C G n) ∪
    FullProductRootFilter.bad P c B L n) ∪ (E \ FixedTargetHalos.good E R n)

def target (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A c B L C G ρ : ℝ) (n : ℕ) : Set ℝ :=
  (E ∩ band P η T A) \ excluded E R Y P c B L C G ρ n

theorem edge_volume {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    volume.real (edge ρ) = 2 * ρ := by
  have hs : Ioo (-1 + ρ) (1 - ρ) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  rw [edge, measureReal_sdiff hs measurableSet_Ioo (by simp),
    Real.volume_real_Icc_of_le (by norm_num), Real.volume_real_Ioo_of_le (by linarith)]
  ring

theorem measurableSet_target {E : Set ℝ} (hE : MeasurableSet E)
    (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A c B L C G ρ : ℝ) (n : ℕ) (hB : 0 < B) (hn : 0 < n) :
    MeasurableSet (target E R Y P η T A c B L C G ρ n) := by
  have hb : MeasurableSet (band P η T A) :=
    (measurableSet_le measurable_const P.continuous.abs.measurable).inter
      (measurableSet_le P.continuous.abs.measurable measurable_const)
  have hg : MeasurableSet (LongSourceGapBound.gaps Y G n) :=
    MeasurableSet.biUnion (LongSourceGapBound.indices Y G n).countable_toSet
      (fun _ _ => measurableSet_Icc)
  exact (hE.inter hb).diff
    (((((measurableSet_Icc.diff measurableSet_Ioo).union (hE.inter hg)).union
      (SourceRankGeometry.measurableSet_shortBadUnion Y C G n)).union
      (FullProductRootFilter.measurableSet_bad P c B L n hB hn)).union
      (hE.diff (FixedTargetHalos.measurableSet_good hE R n)))

theorem excluded_finite {E : Set ℝ} (hEfin : volume E ≠ ⊤)
    (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X]) (c B L C G ρ : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hB : 0 < B) (hL : 0 < L) (hn : 0 < n)
    (hdeg : P.natDegree ≤ 2 * n) :
    volume (excluded E R Y P c B L C G ρ n) ≠ ⊤ := by
  have he : volume (edge ρ) ≠ ⊤ := measure_ne_top_of_subset sdiff_subset (by simp)
  have hg : volume (E ∩ LongSourceGapBound.gaps Y G n) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_left hEfin
  have hr : volume (SourceRankGeometry.shortBadUnion Y C G n) ≠ ⊤ :=
    measure_biUnion_ne_top (SourceRankGeometry.shortBad Y C G n).finite_toSet (fun _ _ => by simp)
  have hp : volume (FullProductRootFilter.bad P c B L n) ≠ ⊤ :=
    ne_of_lt ((FullProductRootFilter.bad_volume_le P c B L n hc hB hL hn hdeg).trans_lt (by simp))
  have hh : volume (E \ FixedTargetHalos.good E R n) ≠ ⊤ :=
    measure_ne_top_of_subset sdiff_subset hEfin
  exact (measure_union_lt_top
    (measure_union_lt_top (measure_union_lt_top (measure_union_lt_top he.lt_top hg.lt_top)
      hr.lt_top) hp.lt_top) hh.lt_top).ne

theorem target_volume_lower {E : Set ℝ} (hEfin : volume E ≠ ⊤)
    (R : ℕ → ℕ) {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (P : ℝ[X]) (η T A c B L C G ρ δ eG eH : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hB : 0 < B) (hL : 0 < L) (hC : 0 < C) (hG : 0 ≤ G)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hn : 0 < n) (hdeg : P.natDegree ≤ 2 * n)
    (hband : δ ≤ volume.real (E ∩ band P η T A))
    (hgap : volume.real (E ∩ LongSourceGapBound.gaps Y G n) ≤ eG)
    (hhalo : volume.real (E \ FixedTargetHalos.good E R n) ≤ eH) :
    δ - (2 * ρ + eG + 12 * G / C + (6 / B + 4 * c + 792 / L) + eH) ≤
      volume.real (target E R Y P η T A c B L C G ρ n) := by
  have he := edge_volume hρ hρ1
  have hr := SourceRankGeometry.shortBadUnion_volume_le hY C G hC hG n hn
  have hp : volume.real (FullProductRootFilter.bad P c B L n) ≤ 6 / B + 4 * c + 792 / L := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (FullProductRootFilter.bad_volume_le P c B L n hc hB hL hn hdeg)
    rw [ENNReal.toReal_ofReal (show 0 ≤ 6 / B + 4 * c + 792 / L by positivity)] at hh
    exact hh
  have h1 := measureReal_union_le (μ := volume) (edge ρ) (E ∩ LongSourceGapBound.gaps Y G n)
  have h2 := measureReal_union_le (μ := volume) (edge ρ ∪ (E ∩ LongSourceGapBound.gaps Y G n))
    (SourceRankGeometry.shortBadUnion Y C G n)
  have h3 := measureReal_union_le (μ := volume) ((edge ρ ∪ (E ∩ LongSourceGapBound.gaps Y G n)) ∪
    SourceRankGeometry.shortBadUnion Y C G n) (FullProductRootFilter.bad P c B L n)
  have h4 := measureReal_union_le (μ := volume) (((edge ρ ∪ (E ∩ LongSourceGapBound.gaps Y G n)) ∪
    SourceRankGeometry.shortBadUnion Y C G n) ∪ FullProductRootFilter.bad P c B L n)
    (E \ FixedTargetHalos.good E R n)
  have hb : volume.real (excluded E R Y P c B L C G ρ n) ≤
      2 * ρ + eG + 12 * G / C + (6 / B + 4 * c + 792 / L) + eH := by
    dsimp only [excluded]
    linarith
  have hd := @le_measureReal_sdiff ℝ _ volume (E ∩ band P η T A)
    (excluded E R Y P c B L C G ρ n)
    (excluded_finite hEfin R Y P c B L C G ρ n hc hB hL hn hdeg)
  change _ ≤ volume.real ((E ∩ band P η T A) \ excluded E R Y P c B L C G ρ n)
  linarith

theorem target_properties {E : Set ℝ} (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X]) (η T A c B L C G ρ : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ target E R Y P η T A c B L C G ρ n) :
    x ∈ E ∧ x ∈ band P η T A ∧ x ∈ Ioo (-1 + ρ) (1 - ρ) ∧
    x ∉ LongSourceGapBound.gaps Y G n ∧ x ∉ SourceRankGeometry.shortBadUnion Y C G n ∧
    x ∉ FullProductRootFilter.bad P c B L n ∧ x ∈ FixedTargetHalos.good E R n := by
  have he : x ∈ E := hx.1.1
  have hnot := hx.2
  change x ∉ (((edge ρ ∪ (E ∩ LongSourceGapBound.gaps Y G n)) ∪
    SourceRankGeometry.shortBadUnion Y C G n) ∪ FullProductRootFilter.bad P c B L n) ∪
    (E \ FixedTargetHalos.good E R n) at hnot
  refine ⟨he, hx.1.2, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra h
    exact hnot (Or.inl (Or.inl (Or.inl (Or.inl ⟨hEI he, h⟩))))
  · intro h
    exact hnot (Or.inl (Or.inl (Or.inl (Or.inr ⟨he, h⟩))))
  · intro h
    exact hnot (Or.inl (Or.inl (Or.inr h)))
  · intro h
    exact hnot (Or.inl (Or.inr h))
  · by_contra h
    exact hnot (Or.inr ⟨he, h⟩)

end Jig133.BandTargetMeasure

end
end File_BandTargetMeasure

section File_BandTargetConstants

/-! # Fixed constants leaving a positive actual retained band -/

noncomputable section
open Set MeasureTheory Polynomial
namespace Jig133.BandTargetConstants
open BandTargetMeasure

def clearance (δ : ℝ) : ℝ := δ / 128
def density (δ : ℝ) : ℝ := 384 / δ
def slope (δ : ℝ) : ℝ := 215040 / δ
def rank (δ G : ℝ) : ℝ := max 1 (384 * G / δ)
def buffer (δ : ℝ) : ℝ := δ / 16

theorem positive {δ : ℝ} (hδ : 0 < δ) (G : ℝ) :
    0 < clearance δ ∧ 0 < density δ ∧ 0 < slope δ ∧ 0 < rank δ G := by
  dsimp [clearance, density, slope, rank]
  exact ⟨by positivity, by positivity, by positivity, lt_of_lt_of_le zero_lt_one (le_max_left _ _)⟩

theorem deletion_budget {δ : ℝ} (hδ : 0 < δ) (G : ℝ) :
    2 * buffer δ + δ / 16 + 12 * G / rank δ G +
      (6 / density δ + 4 * clearance δ + 792 / slope δ) + δ / 32 ≤ δ / 2 := by
  have hC := (positive hδ G).2.2.2
  have hmax : 384 * G / δ ≤ rank δ G := le_max_right _ _
  have hmul := (div_le_iff₀ hδ).mp hmax
  have hr : 12 * G / rank δ G ≤ δ / 32 := by
    apply (div_le_iff₀ hC).mpr
    nlinarith
  have hB : 6 / density δ = δ / 64 := by dsimp [density]; field_simp; norm_num
  have hL : 792 / slope δ = 33 * δ / 8960 := by dsimp [slope]; field_simp; norm_num
  rw [hB, hL]
  dsimp only [clearance, buffer]
  linarith

def retained (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A δ G : ℝ) (n : ℕ) : Set ℝ :=
  target E R Y P η T A (clearance δ) (density δ) (slope δ) (rank δ G) G (buffer δ) n

theorem retained_volume {E : Set ℝ} (hEfin : volume E ≠ ⊤)
    (R : ℕ → ℕ) {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (P : ℝ[X]) (η T A δ G : ℝ) (n : ℕ) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hG : 0 ≤ G) (hn : 0 < n) (hdeg : P.natDegree ≤ 2 * n)
    (hband : δ ≤ volume.real (E ∩ band P η T A))
    (hgap : volume.real (E ∩ LongSourceGapBound.gaps Y G n) ≤ δ / 16)
    (hhalo : volume.real (E \ FixedTargetHalos.good E R n) ≤ δ / 32) :
    δ / 2 ≤ volume.real (retained E R Y P η T A δ G n) := by
  obtain ⟨hc, hB, hL, hC⟩ := positive hδ G
  have hρ : 0 ≤ buffer δ := by dsimp [buffer]; positivity
  have hρ1 : buffer δ ≤ 1 := by dsimp [buffer]; linarith
  have hm := target_volume_lower hEfin R hY P η T A (clearance δ) (density δ)
    (slope δ) (rank δ G) G (buffer δ) δ (δ / 16) (δ / 32) n
    hc.le hB hL hC hG hρ hρ1 hn hdeg hband hgap hhalo
  have hb := deletion_budget hδ G
  change δ / 2 ≤ volume.real (target E R Y P η T A (clearance δ) (density δ)
    (slope δ) (rank δ G) G (buffer δ) n)
  linarith

theorem retained_avoids_sources {E : Set ℝ} (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X]) (hP : P ≠ 0)
    (η T A δ G : ℝ) (n : ℕ) (hδ : 0 < δ) (hn : 0 < n)
    (hroots : ∀ y ∈ Y, P.eval y = 0) :
    ∀ x ∈ retained E R Y P η T A δ G n, x ∉ Y := by
  intro x hx hxY
  obtain ⟨_, _, _, _, _, hbad, _⟩ := target_properties hEI R Y P η T A
    (clearance δ) (density δ) (slope δ) (rank δ G) G (buffer δ) n hx
  obtain ⟨hc, hB, hL, _⟩ := positive hδ G
  have ha := (FullProductBandScale.width_bounds hc hB hL).1
  have hz := (FullProductRootFilter.local_control P hP (clearance δ) (density δ)
    (slope δ) x n hc hB hL hn hbad x (by simp; positivity)).1
  exact hz (hroots x hxY)

end Jig133.BandTargetConstants

end
end File_BandTargetConstants

section File_SparseSourceRows

/-!
# Actual sparse original rows from failure of uniform source counting

The source-count condition is the ordered closed-interval version of SC.
Its negation yields witnesses at every positive accuracy and arbitrary late
cutoff. A recursive choice enforces strictly increasing original row indices.
No source-count theorem or block assertion is assumed as an extra premise.
-/

open Set MeasureTheory
noncomputable section

namespace Jig133.SparseSourceRows
open FiniteSourceNets
attribute [local instance] Classical.propDecidable

/-- The set of all original indexed nodes; the row denominator remains n. -/
def rowNodes (nodes : (n : ℕ) → Fin n → ℝ) (n : ℕ) : Finset ℝ :=
  Finset.univ.image (nodes n)

/-- The net covers every original index, also when some node values repeat. -/
theorem sourceNet_covers_index (nodes : (n : ℕ) → Fin n → ℝ)
    {n : ℕ} {Y : Finset ℝ} {ρ : ℝ}
    (hY : IsSourceNet (rowNodes nodes n) Y ρ) (i : Fin n) :
    ∃ y ∈ Y, |nodes n i - y| < ρ := by
  apply hY.2.2
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Constants precede the row, every actual maximal net, and every supplied
ordered interval representation. The interval family need not be disjoint. -/
def SourceCountAt (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) (δ : ℝ) : Prop :=
  ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∀ Y : Finset ℝ,
      IsSourceNet (rowNodes nodes n) Y (1 / (n : ℝ)) →
      ∀ D : ℕ, ∀ a b : Fin D → ℝ,
        (∀ i, a i ≤ b i) → (D : ℝ) ≤ c * (n : ℝ) →
        δ ≤ volume.real (E ∩ window a b) →
        η * (n : ℝ) ≤ ((Y.filter (fun x => x ∈ window a b)).card : ℝ)

/-- The complete source-count condition over positive mass thresholds. -/
def SourceCount (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ volume.real E → SourceCountAt nodes E δ

/-- Failure produces an actual violating row past any cutoff. All original
node, net, endpoint, complexity and mass data occur in the conclusion. -/
theorem exists_violating_row (nodes : (n : ℕ) → Fin n → ℝ)
    (E : Set ℝ) (δ : ℝ) (hnot : ¬ SourceCountAt nodes E δ)
    (η c : ℝ) (hη : 0 < η) (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, max 1 N ≤ n ∧ ∃ Y : Finset ℝ,
      IsSourceNet (rowNodes nodes n) Y (1 / (n : ℝ)) ∧
      ∃ D : ℕ, ∃ a b : Fin D → ℝ,
        (∀ i, a i ≤ b i) ∧ (D : ℝ) ≤ c * (n : ℝ) ∧
        δ ≤ volume.real (E ∩ window a b) ∧
        ((Y.filter (fun x => x ∈ window a b)).card : ℝ) < η * (n : ℝ) := by
  classical
  by_contra h
  apply hnot
  refine ⟨η, c, hη, hc, max 1 N, le_max_left _ _, ?_⟩
  intro n hn Y hY D a b hab hD hmass
  by_contra hcount
  exact h ⟨n, hn, Y, hY, D, a, b, hab, hD, hmass, lt_of_not_ge hcount⟩

/-- Actual finite witness data, with endpoints indexed by its own interval count. -/
structure Row where
  n : ℕ
  Y : Finset ℝ
  D : ℕ
  a : Fin D → ℝ
  b : Fin D → ℝ

/-- Sparse bounds at accuracy 1/(j+1), always normalized by the original row. -/
def GoodRow (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) (δ : ℝ)
    (j : ℕ) (R : Row) : Prop :=
  IsSourceNet (rowNodes nodes R.n) R.Y (1 / (R.n : ℝ)) ∧
    (∀ i, R.a i ≤ R.b i) ∧
    (R.D : ℝ) / (R.n : ℝ) ≤ 1 / ((j : ℝ) + 1) ∧
    ((R.Y.filter (fun x => x ∈ window R.a R.b)).card : ℝ) / (R.n : ℝ) <
      1 / ((j : ℝ) + 1) ∧
    δ ≤ volume.real (E ∩ window R.a R.b)

theorem exists_sparse_row (nodes : (n : ℕ) → Fin n → ℝ)
    (E : Set ℝ) (δ : ℝ) (hnot : ¬ SourceCountAt nodes E δ) (j N : ℕ) :
    ∃ R : Row, max 1 N ≤ R.n ∧ GoodRow nodes E δ j R := by
  have he : 0 < 1 / ((j : ℝ) + 1) :=
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)
  obtain ⟨n, hn, Y, hY, D, a, b, hab, hD, hmass, hcount⟩ :=
    exists_violating_row nodes E δ hnot _ _ he he N
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 N).trans hn))
  refine ⟨⟨n, Y, D, a, b⟩, hn, hY, hab, ?_, ?_, hmass⟩
  · exact (div_le_iff₀ hnpos).mpr hD
  · exact (div_lt_iff₀ hnpos).mpr hcount

/-- The cutoff function is fixed before all rows. The actual recursion also
forces each chosen original row past the preceding chosen original row. -/
theorem exists_sparse_row_sequence (nodes : (n : ℕ) → Fin n → ℝ)
    (E : Set ℝ) (δ : ℝ) (hnot : ¬ SourceCountAt nodes E δ) (M : ℕ → ℕ) :
    ∃ F : ℕ → Row, StrictMono (fun j => (F j).n) ∧
      ∀ j, max 1 (M j) ≤ (F j).n ∧ GoodRow nodes E δ j (F j) := by
  classical
  let pick (j N : ℕ) : Row := (exists_sparse_row nodes E δ hnot j N).choose
  have hpick (j N : ℕ) : max 1 N ≤ (pick j N).n ∧
      GoodRow nodes E δ j (pick j N) :=
    (exists_sparse_row nodes E δ hnot j N).choose_spec
  let F : ℕ → Row := fun j => Nat.rec (pick 0 (M 0))
    (fun k R => pick (k + 1) (max (R.n + 1) (M (k + 1)))) j
  have hzero : F 0 = pick 0 (M 0) := rfl
  have hsucc (j : ℕ) : F (j + 1) =
      pick (j + 1) (max ((F j).n + 1) (M (j + 1))) := rfl
  refine ⟨F, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro j
    rw [hsucc]
    have h := (hpick (j + 1) (max ((F j).n + 1) (M (j + 1)))).1
    apply Nat.lt_of_succ_le
    exact (le_max_left ((F j).n + 1) (M (j + 1))).trans
      ((le_max_right 1 _).trans h)
  · intro j
    cases j with
    | zero => rw [hzero]; exact hpick 0 (M 0)
    | succ j =>
      rw [hsucc]
      have h := hpick (j + 1) (max ((F j).n + 1) (M (j + 1)))
      exact ⟨(max_le_max le_rfl (le_max_right _ _)).trans h.1, h.2⟩

/-- Unbundled original rows and actual interval endpoint arrays, ready for
clipping by an approximation whose finite complexity was chosen beforehand. -/
theorem exists_sparse_rows (nodes : (n : ℕ) → Fin n → ℝ)
    (E : Set ℝ) (δ : ℝ) (hnot : ¬ SourceCountAt nodes E δ) (M : ℕ → ℕ) :
    ∃ n : ℕ → ℕ, ∃ Y : ℕ → Finset ℝ, ∃ D : ℕ → ℕ,
      ∃ a b : (j : ℕ) → Fin (D j) → ℝ,
        StrictMono n ∧ ∀ j,
          max 1 (M j) ≤ n j ∧
          IsSourceNet (rowNodes nodes (n j)) (Y j) (1 / (n j : ℝ)) ∧
          (∀ i, a j i ≤ b j i) ∧
          (D j : ℝ) / (n j : ℝ) ≤ 1 / ((j : ℝ) + 1) ∧
          (((Y j).filter (fun x => x ∈ window (a j) (b j))).card : ℝ) / (n j : ℝ) <
            1 / ((j : ℝ) + 1) ∧
          δ ≤ volume.real (E ∩ window (a j) (b j)) := by
  obtain ⟨F, hmono, hF⟩ := exists_sparse_row_sequence nodes E δ hnot M
  exact ⟨fun j => (F j).n, fun j => (F j).Y, fun j => (F j).D,
    fun j => (F j).a, fun j => (F j).b, hmono, hF⟩

/-- The positive mass threshold is extracted once, before every accuracy,
cutoff, original row, source net and interval endpoint. -/
theorem not_sourceCount_iff (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) :
    ¬ SourceCount nodes E ↔
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ volume.real E ∧ ¬ SourceCountAt nodes E δ := by
  classical
  constructor
  · intro h
    by_contra h'
    apply h
    intro δ hδ hδE
    by_contra hδcount
    exact h' ⟨δ, hδ, hδE, hδcount⟩
  · rintro ⟨δ, hδ, hδE, hnot⟩ h
    exact hnot (h δ hδ hδE)

/-- Full negation of SC supplies a single positive threshold and actual sparse
sequences for every cutoff function fixed before those sequences. -/
theorem exists_sparse_rows_of_not_sourceCount
    (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) (hnot : ¬ SourceCount nodes E) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ volume.real E ∧ ∀ M : ℕ → ℕ,
      ∃ n : ℕ → ℕ, ∃ Y : ℕ → Finset ℝ, ∃ D : ℕ → ℕ,
        ∃ a b : (j : ℕ) → Fin (D j) → ℝ,
          StrictMono n ∧ ∀ j,
            max 1 (M j) ≤ n j ∧
            IsSourceNet (rowNodes nodes (n j)) (Y j) (1 / (n j : ℝ)) ∧
            (∀ i, a j i ≤ b j i) ∧
            (D j : ℝ) / (n j : ℝ) ≤ 1 / ((j : ℝ) + 1) ∧
            (((Y j).filter (fun x => x ∈ window (a j) (b j))).card : ℝ) / (n j : ℝ) <
              1 / ((j : ℝ) + 1) ∧
            δ ≤ volume.real (E ∩ window (a j) (b j)) := by
  obtain ⟨δ, hδ, hδE, hδnot⟩ := (not_sourceCount_iff nodes E).mp hnot
  exact ⟨δ, hδ, hδE, fun M => exists_sparse_rows nodes E δ hδnot M⟩

end Jig133.SparseSourceRows

end
end File_SparseSourceRows

section File_SourceGapConsequence

/-!
# Uniform short-source-gap control from the actual source-count condition

The cutoff precedes the row and every maximal source net. Closed long gaps
include their endpoints, so the estimate also bounds open complementary gaps.
-/

noncomputable section
open Set MeasureTheory
namespace Jig133.SourceGapConsequence
open FiniteSourceNets SparseSourceRows
attribute [local instance] Classical.propDecidable

abbrev I := Icc (-1 : ℝ) 1

def ShortSourceGaps (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ H : ℝ, 0 < H ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∀ Y : Finset ℝ,
      IsSourceNet (rowNodes nodes n) Y (1 / (n : ℝ)) →
      ∀ H' : ℝ, H ≤ H' → volume.real (E ∩ LongSourceGapBound.gaps Y H' n) < δ

theorem source_net_in_interval
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ I)
    {n : ℕ} {Y : Finset ℝ} {ρ : ℝ} (hY : IsSourceNet (rowNodes nodes n) Y ρ) :
    ∀ y ∈ Y, y ∈ I := by
  intro y hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hY.1 hy)
  exact hsupp n i

/-- Endpoint counts and the total length bound contradict the SC lower count. -/
theorem small_long_gaps_of_sourceCountAt
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ I)
    (E : Set ℝ) {δ : ℝ} (hSC : SourceCountAt nodes E δ) :
    ∃ H : ℝ, 0 < H ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ Y : Finset ℝ,
        IsSourceNet (rowNodes nodes n) Y (1 / (n : ℝ)) →
        volume.real (E ∩ LongSourceGapBound.gaps Y H n) < δ := by
  obtain ⟨η, c, hη, hc, N, hN, hcount⟩ := hSC
  let H := max (4 / c) (8 / η)
  have hH : 0 < H := (div_pos (by norm_num) hc).trans_le (le_max_left _ _)
  have hcH : 4 ≤ H * c := (div_le_iff₀ hc).mp (le_max_left _ _)
  have hηH : 8 ≤ H * η := (div_le_iff₀ hη).mp (le_max_right _ _)
  refine ⟨H, hH, N, hN, ?_⟩
  intro n hn Y hY
  have hnpos : 0 < n := (by omega)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  obtain ⟨D, a, b, hab, heq, hcard, hbudget⟩ := LongSourceGapBound.exists_windows
    (source_net_in_interval nodes hsupp hY) H hnpos
  have hcHn := mul_le_mul_of_nonneg_right hcH hn0.le
  have hD : (D : ℝ) ≤ c * n := by
    apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith only [hbudget, hcHn, hn0]
  by_contra hlarge
  have hmass : δ ≤ volume.real (E ∩ window a b) := by
    rw [heq]
    exact le_of_not_gt hlarge
  have hlow := hcount n hn Y hY D a b hab hD hmass
  have hupp : ((Y.filter (fun x => x ∈ window a b)).card : ℝ) ≤ 2 * D := by
    exact_mod_cast hcard
  have hlowH := mul_le_mul_of_nonneg_right (hlow.trans hupp) hH.le
  have hηHn := mul_le_mul_of_nonneg_right hηH hn0.le
  nlinarith only [hlowH, hηHn, hbudget, hn0]

/-- Complete uniform gap control, including tolerances larger than |E|. -/
theorem shortSourceGaps_of_sourceCount
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ I)
    (E : Set ℝ) (hEI : E ⊆ I) (hSC : SourceCount nodes E) :
    ShortSourceGaps nodes E := by
  intro δ hδ
  have hEfin : volume E ≠ ⊤ := measure_ne_top_of_subset hEI (by simp [I])
  by_cases hmass : δ ≤ volume.real E
  · obtain ⟨H, hH, N, hN, hsmall⟩ :=
      small_long_gaps_of_sourceCountAt nodes hsupp E (hSC δ hδ hmass)
    refine ⟨H, hH, N, hN, ?_⟩
    intro n hn Y hY H' hHH'
    apply lt_of_le_of_lt ?_ (hsmall n hn Y hY)
    exact measureReal_mono
      (inter_subset_inter_right _ (LongSourceGapBound.gaps_antitone Y hHH' n))
      (measure_ne_top_of_subset inter_subset_left hEfin)
  · refine ⟨1, by norm_num, 1, le_rfl, ?_⟩
    intro n _ Y _ H' _
    exact (measureReal_mono (μ := volume) inter_subset_left hEfin).trans_lt
      (lt_of_not_ge hmass)

end Jig133.SourceGapConsequence

end
end File_SourceGapConsequence

section File_BandTargetCutoffs

/-!
# Uniform retained-band cutoffs from the actual source-count condition

The halo sequence is chosen before delta and every later polynomial. The gap
cutoff depends on delta but precedes n, the source net and the full product.
-/

noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped Topology
namespace Jig133.BandTargetCutoffs
open BandTargetMeasure BandTargetConstants FiniteSourceNets SparseSourceRows

theorem exists_uniform_cutoffs
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ Icc (-1 : ℝ) 1)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (hSC : SourceCount nodes E) :
    ∃ R : ℕ → ℕ, (∀ n, 0 < R n) ∧ Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun n : ℕ => (R n : ℝ) / n) atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ G : ℝ, 0 < G ∧
        ∀ᶠ n : ℕ in atTop, 0 < n ∧ G / (n : ℝ) ≤ buffer δ ∧
          FullProductBandScale.width (clearance δ) (density δ) (slope δ) ≤ R n ∧
          ∀ Y : Finset ℝ, IsSourceNet (rowNodes nodes n) Y (1 / (n : ℝ)) →
          ∀ P : ℝ[X], ∀ η T A : ℝ, P.natDegree ≤ 2 * n →
            δ ≤ volume.real (E ∩ band P η T A) →
            δ / 2 ≤ volume.real (retained E R Y P η T A δ G n) := by
  have hfin : volume E ≠ ⊤ := measure_ne_top_of_subset hEI (by simp)
  obtain ⟨R, hpos, hmono, htop, hratio, hbad⟩ := FixedTargetHalos.exists_halos hE hfin
  refine ⟨R, hpos, hmono, htop, hratio, ?_⟩
  intro δ hδ hδ2
  have hSG := SourceGapConsequence.shortSourceGaps_of_sourceCount nodes hsupp E hEI hSC
  obtain ⟨G, hG, N, hN, hgap⟩ := hSG (δ / 16) (by positivity)
  refine ⟨G, hG, ?_⟩
  have hρ : 0 < buffer δ := by dsimp [buffer]; positivity
  have hscale := (tendsto_const_div_atTop_nhds_zero_nat G).eventually_le_const hρ
  have hhalo := hbad.eventually_le_const (show (0 : ℝ) < δ / 32 by positivity)
  have ht : Tendsto (fun n => (R n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp htop
  have hwidth := ht.eventually_ge_atTop
    (FullProductBandScale.width (clearance δ) (density δ) (slope δ))
  filter_upwards [eventually_ge_atTop N, hscale, hhalo, hwidth] with n hn hs hh hw
  have hnpos : 0 < n := by omega
  refine ⟨hnpos, hs, hw, ?_⟩
  intro Y hY P η T A hdeg hband
  exact retained_volume hfin R (SourceGapConsequence.source_net_in_interval nodes hsupp hY)
    P η T A δ G n hδ hδ2 hG.le hnpos hdeg hband (hgap n hn Y hY G le_rfl).le hh

end Jig133.BandTargetCutoffs

end
end File_BandTargetCutoffs

section File_SourceGapWindowHalos

/-! # Actual selected-window leakage into the complement of the fixed target -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace Jig133.SourceGapWindowHalos
open SourceGapSelection SourceGapWindows
attribute [local instance] Classical.propDecidable

def anchors (Y : Finset ℝ) (Q : Set ℝ) : Finset ℝ := (indices Y Q).image (anchor Y Q)

theorem anchors_card (Y : Finset ℝ) (Q : Set ℝ) : (anchors Y Q).card ≤ Y.card :=
  Finset.card_image_le.trans (SourceGapSelection.card_le Y Q)

theorem anchors_good {E Q : Set ℝ} (R : ℕ → ℕ) (Y : Finset ℝ) (n : ℕ)
    (hQ : Q ⊆ FixedTargetHalos.good E R n) :
    ∀ x ∈ anchors Y Q, x ∈ FixedTargetHalos.good E R n := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact hQ (anchor_mem Y Q i hi).1

theorem windows_subset_halos (R : ℕ → ℕ) (Y : Finset ℝ) (Q : Set ℝ)
    (c B L : ℝ) (n : ℕ) (hscale : FullProductBandScale.width c B L ≤ R n) :
    windows Y Q c B L n ⊆ FixedTargetHalos.halos R n (anchors Y Q) := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  refine mem_iUnion₂.mpr ⟨anchor Y Q i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  have hd : |x - anchor Y Q i| ≤ FullProductBandScale.width c B L / n := by
    rw [abs_le]
    constructor <;> linarith [hxi.1, hxi.2]
  exact hd.trans (div_le_div_of_nonneg_right hscale (Nat.cast_nonneg n))

theorem windows_leak {E Q : Set ℝ} (R : ℕ → ℕ) (Y : Finset ℝ)
    (c B L : ℝ) (n : ℕ) (hn : 0 < n) (hR : 0 < R n)
    (hcard : Y.card ≤ n) (hQ : Q ⊆ FixedTargetHalos.good E R n)
    (hscale : FullProductBandScale.width c B L ≤ R n) :
    volume.real (windows Y Q c B L n \ E) ≤ 1 / (R n : ℝ) :=
  LocalHaloBudget.subset_leak_le hn hR (anchors Y Q)
    ((anchors_card Y Q).trans hcard) (anchors_good R Y n hQ)
    (windows_subset_halos R Y Q c B L n hscale)

theorem eventually_windows_leak {E : Set ℝ} {R : ℕ → ℕ}
    (hpos : ∀ n, 0 < R n) (htop : Tendsto R atTop atTop) (c B L : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ Y : Finset ℝ, ∀ Q : Set ℝ, Y.card ≤ n →
      Q ⊆ FixedTargetHalos.good E R n →
      volume.real (windows Y Q c B L n \ E) ≤ 1 / (R n : ℝ) := by
  have ht : Tendsto (fun n => (R n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp htop
  filter_upwards [ht.eventually_ge_atTop (FullProductBandScale.width c B L),
    eventually_ge_atTop 1] with n hs hn
  intro Y Q hcard hQ
  exact windows_leak R Y c B L n (by omega) (hpos n) hcard hQ hs

end Jig133.SourceGapWindowHalos

end
end File_SourceGapWindowHalos

section File_BandWindowExtraction

/-! # Actual positive window families from a full-product band -/

noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped Topology
namespace Jig133.BandWindowExtraction
open BandTargetMeasure BandTargetConstants FiniteSourceNets SparseSourceRows

def region (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A δ G : ℝ) (n : ℕ) : Set ℝ :=
  SourceGapWindows.windows Y (retained E R Y P η T A δ G n)
    (clearance δ) (density δ) (slope δ) n

theorem region_compact (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A δ G : ℝ) (n : ℕ) : IsCompact (region E R Y P η T A δ G n) :=
  (SourceGapSelection.indices Y (retained E R Y P η T A δ G n)).isCompact_biUnion
    (fun _ _ => isCompact_Icc)

theorem row_facts {E : Set ℝ} (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (R : ℕ → ℕ) {Y : Finset ℝ} (hY : ∀ y ∈ Y, y ∈ Icc (-1 : ℝ) 1)
    (P : ℝ[X]) (hP : P ≠ 0) (η T A δ G : ℝ) (n : ℕ)
    (hδ : 0 < δ) (hG : 0 < G) (hn : 0 < n) (hR : 0 < R n)
    (hcard : Y.card ≤ n) (hroots : ∀ y ∈ Y, P.eval y = 0)
    (hscale : G / (n : ℝ) ≤ buffer δ)
    (hwidth : FullProductBandScale.width (clearance δ) (density δ) (slope δ) ≤ R n)
    (hmass : δ / 2 ≤ volume.real (retained E R Y P η T A δ G n)) :
    region E R Y P η T A δ G n ⊆ Icc (-1 : ℝ) 1 ∧
    FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G ≤
      volume.real (region E R Y P η T A δ G n) ∧
    volume.real (region E R Y P η T A δ G n \ E) ≤ 1 / (R n : ℝ) ∧
    ∀ x ∈ region E R Y P η T A δ G n,
      (η * Real.exp (-(1 / 2 : ℝ))) * A ≤ |P.eval x| ∧
      |P.eval x| ≤ (T * Real.exp (1 / 2 : ℝ)) * A := by
  let Q := retained E R Y P η T A δ G n
  obtain ⟨hc, hB, hL, _⟩ := positive hδ G
  have hprops (q : ℝ) (hq : q ∈ Q) := target_properties hEI R Y P η T A
    (clearance δ) (density δ) (slope δ) (rank δ G) G (buffer δ) n hq
  have hbad (q : ℝ) (hq : q ∈ Q) := (hprops q hq).2.2.2.2.2.1
  have hgood : Q ⊆ FixedTargetHalos.good E R n := fun q hq => (hprops q hq).2.2.2.2.2.2
  have hband (q : ℝ) (hq : q ∈ Q) := (hprops q hq).2.1
  have hsource : ∀ q ∈ Q, q ∉ Y := retained_avoids_sources hEI R Y P hP η T A δ G n hδ hn hroots
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hg := SourceGapWindows.window_subset_gap Y Q P hP (clearance δ) (density δ)
      (slope δ) n hc hB hL hn hroots hbad i hi hxi
    exact FiniteSourceGaps.gap_in_interval hY i ⟨hg.1.le, hg.2.le⟩
  · have hm := SourceGapWindows.actual_volume_lower hY Q P hP (clearance δ) (density δ)
      (slope δ) G (δ / 2) (buffer δ) n hc hB hL hG hn
      (by dsimp [buffer]; positivity) hscale hroots hbad
      (fun q hq => (hprops q hq).2.2.1) hsource
      (fun q hq => (hprops q hq).2.2.2.1) hmass
    calc
      _ = 2 * FullProductBandScale.width (clearance δ) (density δ) (slope δ) * (δ / 2) / G := by ring
      _ ≤ _ := hm
  · exact SourceGapWindowHalos.windows_leak R Y (clearance δ) (density δ) (slope δ)
      n hn hR hcard hgood hwidth
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact SourceGapWindows.window_band Y Q P hP (clearance δ) (density δ) (slope δ)
      η T A n hc hB hL hn hbad hband i hi x hxi

theorem exists_uniform_windows
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ Icc (-1 : ℝ) 1)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (hSC : SourceCount nodes E) :
    ∃ R : ℕ → ℕ, (∀ n, 0 < R n) ∧ Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun n : ℕ => (R n : ℝ) / n) atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ G : ℝ, 0 < G ∧
        ∀ᶠ n : ℕ in atTop, ∀ Y : Finset ℝ,
          IsSourceNet (rowNodes nodes n) Y (1 / (n : ℝ)) →
          ∀ P : ℝ[X], P ≠ 0 → (∀ i, P.eval (nodes n i) = 0) →
          ∀ η T A : ℝ, P.natDegree ≤ 2 * n → δ ≤ volume.real (E ∩ band P η T A) →
          region E R Y P η T A δ G n ⊆ Icc (-1 : ℝ) 1 ∧
          FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G ≤
            volume.real (region E R Y P η T A δ G n) ∧
          volume.real (region E R Y P η T A δ G n \ E) ≤ 1 / (R n : ℝ) ∧
          ∀ x ∈ region E R Y P η T A δ G n,
            (η * Real.exp (-(1 / 2 : ℝ))) * A ≤ |P.eval x| ∧
            |P.eval x| ≤ (T * Real.exp (1 / 2 : ℝ)) * A := by
  obtain ⟨R, hpos, hmono, htop, hratio, hcut⟩ :=
    BandTargetCutoffs.exists_uniform_cutoffs nodes hsupp E hE hEI hSC
  refine ⟨R, hpos, hmono, htop, hratio, ?_⟩
  intro δ hδ hδ2
  obtain ⟨G, hG, hlate⟩ := hcut δ hδ hδ2
  refine ⟨G, hG, ?_⟩
  filter_upwards [hlate] with n hn
  intro Y hY P hP hroots η T A hdeg hband
  have hcard : Y.card ≤ n := calc
    _ ≤ (rowNodes nodes n).card := Finset.card_le_card hY.1
    _ ≤ n := by simpa only [rowNodes, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := nodes n))
  have hyroots : ∀ y ∈ Y, P.eval y = 0 := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hY.1 hy)
    exact hroots i
  exact row_facts hEI R (SourceGapConsequence.source_net_in_interval nodes hsupp hY)
    P hP η T A δ G n hδ hG hn.1 (hpos n) hcard hyroots hn.2.1 hn.2.2.1
    (hn.2.2.2 Y hY P η T A hdeg hband)

end Jig133.BandWindowExtraction

end
end File_BandWindowExtraction

section File_DominatedDensityTarget

/-!
# A compact target with an actual positive density lower bound

A finite measure dominated by volume on [-1,1] has an actual Radon--Nikodym
density between zero and one almost everywhere. Positive mass on a measurable set forces a
quantitatively positive density level there. Inner regularity supplies a
compact subset, and the actual density represents the original measure.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Jig133.DominatedDensityTarget

abbrev I : Set ℝ := Icc (-1 : ℝ) 1

abbrev reference : Measure ℝ := volume.restrict I

/-- The actual real-valued Radon--Nikodym derivative relative to interval volume. -/
def density (μ : FiniteMeasure ℝ) (x : ℝ) : ℝ :=
  ((μ : Measure ℝ).rnDeriv reference x).toReal

theorem measurable_density (μ : FiniteMeasure ℝ) : Measurable (density μ) :=
  (Measure.measurable_rnDeriv (μ : Measure ℝ) reference).ennreal_toReal

theorem density_nonneg (μ : FiniteMeasure ℝ) (x : ℝ) : 0 ≤ density μ x :=
  ENNReal.toReal_nonneg

/-- Domination, rather than a supplied density bound, gives the upper bound. -/
theorem ae_density_le_one (μ : FiniteMeasure ℝ)
    (hdom : (μ : Measure ℝ) ≤ reference) :
    ∀ᵐ x ∂reference, density μ x ≤ 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le hdom] with x hx
  change (μ : Measure ℝ).rnDeriv reference x ≤ (1 : ℝ≥0∞) at hx
  have h := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hx
  simpa only [density, ENNReal.toReal_one] using h

theorem integrable_density (μ : FiniteMeasure ℝ) :
    Integrable (density μ) reference := by
  exact integrableOn_univ.mp
    (Measure.integrableOn_toReal_rnDeriv (ν := reference)
      (measure_ne_top (μ : Measure ℝ) univ))

/-- The actual density recovers each original set mass. -/
theorem setIntegral_density (μ : FiniteMeasure ℝ)
    (hdom : (μ : Measure ℝ) ≤ reference) (E : Set ℝ) :
    (∫ x in E, density μ x ∂reference) = (μ : Measure ℝ).real E := by
  exact Measure.setIntegral_toReal_rnDeriv
    (Measure.absolutelyContinuous_of_le hdom) E

/-- A δ/4 density level captures at least δ/2 of reference measure.
Only the original positive mass and domination are inputs. -/
theorem density_level_mass (μ : FiniteMeasure ℝ)
    (hdom : (μ : Measure ℝ) ≤ reference) (E : Set ℝ) (hE : MeasurableSet E)
    (δ : ℝ) (hδ : 0 ≤ δ) (hmass : δ ≤ (μ : Measure ℝ).real E) :
    δ / 2 ≤ reference.real ((E ∩ I) ∩ {x | δ / 4 ≤ density μ x}) := by
  classical
  let S : Set ℝ := (E ∩ I) ∩ {x | δ / 4 ≤ density μ x}
  have hS : MeasurableSet S :=
    (hE.inter measurableSet_Icc).inter
      (measurableSet_le measurable_const (measurable_density μ))
  have hI : ∀ᵐ x ∂reference, x ∈ I := ae_restrict_mem measurableSet_Icc
  have hpoint : E.indicator (density μ) ≤ᵐ[reference]
      (fun x => δ / 4 + S.indicator (fun _ : ℝ => (1 : ℝ)) x) := by
    filter_upwards [ae_density_le_one μ hdom, hI] with x hx hxI
    by_cases hxE : x ∈ E
    · by_cases hxlevel : δ / 4 ≤ density μ x
      · have hxS : x ∈ S := ⟨⟨hxE, hxI⟩, hxlevel⟩
        simp only [indicator_of_mem hxE, indicator_of_mem hxS]
        linarith
      · have hxS : x ∉ S := fun h => hxlevel h.2
        simp only [indicator_of_mem hxE, indicator_of_notMem hxS, add_zero]
        exact (lt_of_not_ge hxlevel).le
    · have hxS : x ∉ S := fun h => hxE h.1.1
      simp only [indicator_of_notMem hxE, indicator_of_notMem hxS, add_zero]
      exact div_nonneg hδ (by norm_num)
  have hind : Integrable (fun x => S.indicator (fun _ : ℝ => (1 : ℝ)) x)
      reference := (integrable_const (1 : ℝ)).indicator hS
  have hineq := integral_mono_ae ((integrable_density μ).indicator hE)
    ((integrable_const (δ / 4)).add hind) hpoint
  have hleft : (∫ x, E.indicator (density μ) x ∂reference) =
      (μ : Measure ℝ).real E := by
    rw [integral_indicator hE]
    exact setIntegral_density μ hdom E
  have hright :
      (∫ x, δ / 4 + S.indicator (fun _ : ℝ => (1 : ℝ)) x ∂reference) =
        2 * (δ / 4) + reference.real S := by
    rw [integral_add (integrable_const (δ / 4)) hind, integral_const,
      integral_indicator_const (1 : ℝ) hS]
    have htotal : reference.real univ = 2 := by
      norm_num [reference, I, measureReal_restrict_apply_univ, Real.volume_real_Icc]
    rw [htotal]
    simp only [smul_eq_mul, mul_one]
  change (∫ x, E.indicator (density μ) x ∂reference) ≤
    ∫ x, δ / 4 + S.indicator (fun _ : ℝ => (1 : ℝ)) x ∂reference at hineq
  rw [hleft, hright] at hineq
  change δ / 2 ≤ reference.real S
  linarith

/-- On a measurable subset of a genuine density level, restricted volume is
dominated by the original measure, with the actual coefficient. -/
theorem lower_bound_of_density_level (μ : FiniteMeasure ℝ)
    (hdom : (μ : Measure ℝ) ≤ reference) (K : Set ℝ) (hK : MeasurableSet K)
    (hKI : K ⊆ I) (a : ℝ) (hlevel : ∀ x ∈ K, a ≤ density μ x) :
    ENNReal.ofReal a • volume.restrict K ≤ (μ : Measure ℝ) := by
  have hlower : (fun _ : ℝ => ENNReal.ofReal a) ≤ᵐ[reference.restrict K]
      (μ : Measure ℝ).rnDeriv reference := by
    filter_upwards [ae_restrict_mem hK] with x hx
    exact ENNReal.ofReal_le_of_le_toReal (hlevel x hx)
  have h := withDensity_mono hlower
  rw [withDensity_const, ← restrict_withDensity hK,
    Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hdom)] at h
  have hrestrict : reference.restrict K = volume.restrict K :=
    Measure.restrict_restrict_of_subset hKI
  rw [hrestrict] at h
  exact h.trans Measure.restrict_le_self

/-- Actual compact target extraction with fixed coefficient δ/4 and volume
strictly greater than δ/4. No support-on-E or prescribed density premise is
needed beyond the original measurable E-mass lower bound. -/
theorem exists_compact_density_target (μ : FiniteMeasure ℝ)
    (hdom : (μ : Measure ℝ) ≤ reference) (E : Set ℝ) (hE : MeasurableSet E)
    (δ : ℝ) (hδ : 0 < δ) (hmass : δ ≤ (μ : Measure ℝ).real E) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ E ∩ I ∧
      0 < volume.real K ∧ δ / 4 < volume.real K ∧
      ENNReal.ofReal (δ / 4) • volume.restrict K ≤ (μ : Measure ℝ) := by
  let S : Set ℝ := (E ∩ I) ∩ {x | δ / 4 ≤ density μ x}
  have hS : MeasurableSet S :=
    (hE.inter measurableSet_Icc).inter
      (measurableSet_le measurable_const (measurable_density μ))
  have hmassS : δ / 2 ≤ reference.real S :=
    density_level_mass μ hdom E hE δ hδ.le hmass
  have hquarter : 0 < δ / 4 := div_pos hδ (by norm_num)
  have hcut : ENNReal.ofReal (δ / 4) < reference S := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal hquarter.le
      (measure_ne_top reference S)).mpr
    change δ / 4 < reference.real S
    linarith
  obtain ⟨K, hKS, hK, hmassK⟩ := hS.exists_lt_isCompact hcut
  have hKEI : K ⊆ E ∩ I := fun x hx => (hKS hx).1
  have hKI : K ⊆ I := fun x hx => (hKEI hx).2
  have hreal : reference.real K = volume.real K := by
    rw [reference, measureReal_restrict_apply hK.measurableSet,
      inter_eq_left.mpr hKI]
  have hKquarter : δ / 4 < volume.real K := by
    have h := (ENNReal.ofReal_lt_iff_lt_toReal hquarter.le
      (measure_ne_top reference K)).mp hmassK
    change δ / 4 < reference.real K at h
    rwa [hreal] at h
  refine ⟨K, hK, hKEI, hquarter.trans hKquarter, hKquarter, ?_⟩
  exact lower_bound_of_density_level μ hdom K hK.measurableSet hKI (δ / 4)
    (fun x hx => (hKS hx).2)

end Jig133.DominatedDensityTarget

end
end File_DominatedDensityTarget

section File_DominatedWeakSupport

/-!
# Fixed measurable targets for dominated weak limits

Bounded continuous L1 approximation transfers weak convergence to integrals
against a common finite dominating measure.  For fixed measurable indicators,
the reference measure plus the proposed limit supplies that common domination
without presupposing domination of the limit by the reference measure itself.
This proves setwise convergence, domination of the limit, and support from
vanishing leakage.  The target is fixed; no assertion concerns moving sets.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Jig133.DominatedWeakSupport

/-- Genuine integral comparison bounds both approximation errors uniformly. -/
theorem integral_sub_le_l1 (κ ν : Measure ℝ) (hν : ν ≤ κ)
    (f g : ℝ → ℝ) (hf : Integrable f κ) (hg : Integrable g κ) :
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| ≤ ∫ x, |f x - g x| ∂κ := by
  calc
    _ = |∫ x, f x - g x ∂ν| := by
      rw [integral_sub (hf.mono_measure hν) (hg.mono_measure hν)]
    _ ≤ ∫ x, |f x - g x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, |f x - g x| ∂κ :=
      integral_mono_measure hν (Eventually.of_forall fun x => abs_nonneg _)
        (hf.sub hg).abs

/-- Actual L1 approximation upgrades weak convergence for a fixed integrable
test function when both the sequence and its limit are dominated by κ. -/
theorem tendsto_integral_of_dominated (κ : Measure ℝ) [IsFiniteMeasure κ]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ κ) (hμ : (μ : Measure ℝ) ≤ κ)
    (f : ℝ → ℝ) (hf : Integrable f κ) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure ℝ))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g, happrox, hg⟩ := hf.exists_boundedContinuous_integral_sub_le
    (show 0 < ε / 4 by linarith)
  simp only [Real.norm_eq_abs] at happrox
  have htest := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak g
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htest (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hleft := (integral_sub_le_l1 κ (μs n) (hs n) f g hf hg).trans happrox
  have hright := (integral_sub_le_l1 κ μ hμ f g hf hg).trans happrox
  have hmid := hN n hn
  rw [Real.dist_eq] at hmid ⊢
  have htriangle := dist_triangle4
    (∫ x, f x ∂(μs n : Measure ℝ)) (∫ x, g x ∂(μs n : Measure ℝ))
    (∫ x, g x ∂(μ : Measure ℝ)) (∫ x, f x ∂(μ : Measure ℝ))
  simp only [Real.dist_eq] at htriangle
  rw [abs_sub_comm (∫ x, g x ∂(μ : Measure ℝ))
    (∫ x, f x ∂(μ : Measure ℝ))] at htriangle
  linarith

/-- The mass of every fixed measurable set converges along a uniformly
dominated weakly convergent sequence. Domination of μ by ν is not assumed. -/
theorem tendsto_measureReal (ν : Measure ℝ) [IsFiniteMeasure ν]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (E : Set ℝ) (hE : MeasurableSet E) :
    Tendsto (fun n => (μs n : Measure ℝ).real E) atTop
      (𝓝 ((μ : Measure ℝ).real E)) := by
  let κ : Measure ℝ := ν + (μ : Measure ℝ)
  have hsκ : ∀ n, (μs n : Measure ℝ) ≤ κ :=
    fun n => (hs n).trans (Measure.le_add_right le_rfl)
  have hμκ : (μ : Measure ℝ) ≤ κ := Measure.le_add_left le_rfl
  have hi : Integrable (E.indicator (fun _ : ℝ => (1 : ℝ))) κ :=
    (integrable_const (1 : ℝ)).indicator hE
  have h := tendsto_integral_of_dominated κ μs μ hweak hsκ hμκ _ hi
  simpa only [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one] using h

/-- A weak limit of finite measures bounded by one finite real Borel measure
is itself bounded by that measure. -/
theorem limit_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ ν) : (μ : Measure ℝ) ≤ ν := by
  apply Measure.le_iff.mpr
  intro E hE
  apply (ENNReal.toReal_le_toReal (measure_ne_top (μ : Measure ℝ) E)
    (measure_ne_top ν E)).mp
  exact le_of_tendsto' (tendsto_measureReal ν μs μ hweak hs E hE)
    (fun n => ENNReal.toReal_mono (measure_ne_top ν E) (hs n E))

/-- Vanishing leakage on the complement of a fixed measurable set forces
actual zero limit mass there. No closedness or null-boundary premise is needed. -/
theorem measure_compl_eq_zero_of_leakage (ν : Measure ℝ) [IsFiniteMeasure ν]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0)) :
    (μ : Measure ℝ) Eᶜ = 0 := by
  have hz : (μ : Measure ℝ).real Eᶜ = 0 :=
    tendsto_nhds_unique (tendsto_measureReal ν μs μ hweak hs Eᶜ hE.compl) hleak
  exact (measureReal_eq_zero_iff (measure_ne_top (μ : Measure ℝ) Eᶜ)).mp hz

theorem ae_mem_of_leakage (ν : Measure ℝ) [IsFiniteMeasure ν]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0)) :
    ∀ᵐ x ∂(μ : Measure ℝ), x ∈ E := by
  rw [ae_iff]
  exact measure_compl_eq_zero_of_leakage ν μs μ hweak hs E hE hleak

/-- The fixed target captures all limit mass, including in the zero-mass case. -/
theorem measure_target_eq_univ (ν : Measure ℝ) [IsFiniteMeasure ν]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0)) :
    (μ : Measure ℝ) E = (μ : Measure ℝ) univ := by
  apply measure_eq_measure_of_null_sdiff (subset_univ E)
  simpa only [← compl_eq_univ_sdiff] using
    measure_compl_eq_zero_of_leakage ν μs μ hweak hs E hE hleak

/-- Strictly positive limit mass already gives a positive fixed target. -/
theorem positive_target_of_limit_mass (ν : Measure ℝ) [IsFiniteMeasure ν]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0))
    (hmass : 0 < (μ : Measure ℝ).real univ) :
    0 < (μ : Measure ℝ).real E ∧ 0 < ν.real E := by
  have htarget : (μ : Measure ℝ).real E = (μ : Measure ℝ).real univ :=
    congrArg ENNReal.toReal (measure_target_eq_univ ν μs μ hweak hs E hE hleak)
  have hpos : 0 < (μ : Measure ℝ).real E := htarget.symm ▸ hmass
  exact ⟨hpos, hpos.trans_le (ENNReal.toReal_mono (measure_ne_top ν E)
    (limit_le ν μs μ hweak hs E))⟩

/-- Uniform positive mass yields a quantitative positive fixed target under
the dominating measure; all desired limit properties are proved here. -/
theorem fixed_target_mass (ν : Measure ℝ) [IsFiniteMeasure ν]
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0))
    (δ : ℝ) (hmass : ∀ᶠ n in atTop, δ ≤ (μs n : Measure ℝ).real univ) :
    (μ : Measure ℝ) ≤ ν ∧ (∀ᵐ x ∂(μ : Measure ℝ), x ∈ E) ∧
      δ ≤ (μ : Measure ℝ).real E ∧ δ ≤ ν.real E := by
  have hdom := limit_le ν μs μ hweak hs
  have hlimmass : δ ≤ (μ : Measure ℝ).real univ :=
    ge_of_tendsto (tendsto_measureReal ν μs μ hweak hs univ MeasurableSet.univ) hmass
  have htarget : (μ : Measure ℝ).real E = (μ : Measure ℝ).real univ :=
    congrArg ENNReal.toReal (measure_target_eq_univ ν μs μ hweak hs E hE hleak)
  have hδE : δ ≤ (μ : Measure ℝ).real E := htarget.symm ▸ hlimmass
  exact ⟨hdom, ae_mem_of_leakage ν μs μ hweak hs E hE hleak, hδE,
    hδE.trans (ENNReal.toReal_mono (measure_ne_top ν E) (hdom E))⟩

/-- Concrete interval version for the retained moving-window measures.
The fixed measurable target can have arbitrary boundary and need not be closed. -/
theorem interval_fixed_target (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1))
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ)
    (hmass : ∀ᶠ n in atTop, δ ≤ (μs n : Measure ℝ).real univ) :
    (μ : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1) ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ E) ∧ δ ≤ (μ : Measure ℝ).real E ∧
      δ ≤ volume.real (E ∩ Icc (-1 : ℝ) 1) ∧
      0 < volume.real (E ∩ Icc (-1 : ℝ) 1) := by
  obtain ⟨hdom, hsupport, hμE, hνE⟩ :=
    fixed_target_mass (volume.restrict (Icc (-1 : ℝ) 1)) μs μ hweak hs E hE hleak δ hmass
  have hreal : (volume.restrict (Icc (-1 : ℝ) 1)).real E =
      volume.real (E ∩ Icc (-1 : ℝ) 1) := by
    change ((volume.restrict (Icc (-1 : ℝ) 1)) E).toReal =
      (volume (E ∩ Icc (-1 : ℝ) 1)).toReal
    rw [Measure.restrict_apply hE]
  rw [hreal] at hνE
  exact ⟨hdom, hsupport, hμE, hνE, hδ.trans_le hνE⟩

end Jig133.DominatedWeakSupport

end
end File_DominatedWeakSupport

section File_DominatedMeasureCompactness

/-!
# Actual weak subsequences of interval-dominated finite measures

The original measures may have varying or zero mass. Pullback to the compact
interval is recovered exactly by pushforward. Joint compactness of normalized
probability measures and bounded masses produces the weak subsequence; no
first-countability assumption on the space of finite measures is needed.
The previously proved dominated support theorem then supplies a fixed positive
measurable target from genuine leakage and eventual mass bounds.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace Jig133.DominatedMeasureCompactness

abbrev UnitInterval := Icc (-1 : ℝ) 1

/-- Domination gives an actual total mass bound, with zero mass included. -/
theorem mass_le_two (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1)) :
    μ.mass ≤ 2 := by
  have htotal : (μ : Measure ℝ) univ ≤ (2 : ℝ≥0∞) := by
    calc
      _ ≤ (volume.restrict (Icc (-1 : ℝ) 1)) univ := hμ univ
      _ = 2 := by norm_num [Measure.restrict_apply, Real.volume_Icc]
  change ((μ : Measure ℝ) univ).toNNReal ≤ 2
  exact (ENNReal.toNNReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ∞) htotal).trans_eq (ENNReal.toNNReal_ofNat 2)

/-- Every dominated measure is actually carried by the compact interval. -/
theorem measure_compl_eq_zero (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1)) :
    (μ : Measure ℝ) (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ (volume.restrict (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1)ᶜ := hμ _
    _ = 0 := by rw [Measure.restrict_apply measurableSet_Icc.compl]; simp

/-- The subtype pullback loses no mass or atoms: pushing it forward is μ itself. -/
theorem map_comap_interval (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1)) :
    (μ.comap (Subtype.val : UnitInterval → ℝ)).map Subtype.val = μ := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap]
  rw [map_comap_subtype_coe measurableSet_Icc]
  exact Measure.restrict_eq_self_of_ae_mem (measure_compl_eq_zero μ hμ)

/-- Jointly extract the normalized probability measures and their varying masses
on the actual compact interval, then rescale continuously, including at mass zero. -/
theorem exists_subsequence_on_interval (η : ℕ → FiniteMeasure UnitInterval)
    (C : ℝ≥0) (hη : ∀ n, (η n).mass ≤ C) :
    ∃ ηlim : FiniteMeasure UnitInterval, ∃ α : ℕ → ℕ,
      StrictMono α ∧ Tendsto (fun n => η (α n)) atTop (𝓝 ηlim) := by
  let : Nonempty UnitInterval := ⟨⟨0, by constructor <;> norm_num⟩⟩
  let z (n : ℕ) : ProbabilityMeasure UnitInterval × ℝ≥0 :=
    ((η n).normalize, (η n).mass)
  have hc : IsCompact
      ((univ : Set (ProbabilityMeasure UnitInterval)) ×ˢ Icc (0 : ℝ≥0) C) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨p, _hp, α, hα, hz⟩ := hc.tendsto_subseq (fun n =>
    (show z n ∈ (univ : Set (ProbabilityMeasure UnitInterval)) ×ˢ Icc (0 : ℝ≥0) C from
      ⟨mem_univ _, zero_le, hη n⟩))
  have hprob : Tendsto (fun n => (η (α n)).normalize) atTop (𝓝 p.1) := hz.fst_nhds
  have hmass : Tendsto (fun n => (η (α n)).mass) atTop (𝓝 p.2) := hz.snd_nhds
  have hfinite : Tendsto (fun n => (η (α n)).normalize.toFiniteMeasure)
      atTop (𝓝 p.1.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto p.1).comp hprob
  have hscaled : Tendsto
      (fun n => (η (α n)).mass • (η (α n)).normalize.toFiniteMeasure)
      atTop (𝓝 (p.2 • p.1.toFiniteMeasure)) := hmass.smul hfinite
  have heq : (fun n => (η (α n)).mass • (η (α n)).normalize.toFiniteMeasure) =
      (fun n => η (α n)) := by
    funext n
    exact (η (α n)).self_eq_mass_smul_normalize.symm
  rw [heq] at hscaled
  exact ⟨p.2 • p.1.toFiniteMeasure, α, hα, hscaled⟩

/-- A genuine strictly increasing weak subsequence exists for every sequence
bounded by interval volume, and its actual limit retains that domination. -/
theorem exists_dominated_subsequence (μs : ℕ → FiniteMeasure ℝ)
    (hs : ∀ n, (μs n : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1)) :
    ∃ μ : FiniteMeasure ℝ, ∃ α : ℕ → ℕ, StrictMono α ∧
      Tendsto (fun n => μs (α n)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1) := by
  let η (n : ℕ) : FiniteMeasure UnitInterval :=
    (μs n).comap (Subtype.val : UnitInterval → ℝ)
  have hη : ∀ n, (η n).mass ≤ 2 := fun n =>
    (FiniteMeasure.mass_comap_le _ (μs n)).trans (mass_le_two (μs n) (hs n))
  obtain ⟨ηlim, α, hα, hlim⟩ := exists_subsequence_on_interval η 2 hη
  have hmap := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => η (α n)) ηlim hlim (f := (Subtype.val : UnitInterval → ℝ))
    continuous_subtype_val
  have heq : (fun n => (η (α n)).map (Subtype.val : UnitInterval → ℝ)) =
      (fun n => μs (α n)) := by
    funext n
    exact map_comap_interval (μs (α n)) (hs (α n))
  rw [heq] at hmap
  exact ⟨ηlim.map Subtype.val, α, hα, hmap,
    DominatedWeakSupport.limit_le (volume.restrict (Icc (-1 : ℝ) 1))
      (fun n => μs (α n)) _ hmap (fun n => hs (α n))⟩

/-- Construct the weak subsequence and its quantitative positive fixed target.
The target need only be measurable; no boundary-nullness or closedness is assumed. -/
theorem exists_positive_target (μs : ℕ → FiniteMeasure ℝ)
    (hs : ∀ n, (μs n : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1))
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ)
    (hmass : ∀ᶠ n in atTop, δ ≤ (μs n : Measure ℝ).real univ) :
    ∃ μ : FiniteMeasure ℝ, ∃ α : ℕ → ℕ, StrictMono α ∧
      Tendsto (fun n => μs (α n)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1) ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ E) ∧ δ ≤ (μ : Measure ℝ).real E ∧
      δ ≤ volume.real (E ∩ Icc (-1 : ℝ) 1) ∧
      0 < volume.real (E ∩ Icc (-1 : ℝ) 1) := by
  obtain ⟨μ, α, hα, hweak, hdom⟩ := exists_dominated_subsequence μs hs
  have hleak' : Tendsto (fun n => (μs (α n) : Measure ℝ).real Eᶜ) atTop (𝓝 0) :=
    hleak.comp hα.tendsto_atTop
  have hmass' : ∀ᶠ n in atTop, δ ≤ (μs (α n) : Measure ℝ).real univ :=
    hα.tendsto_atTop.eventually hmass
  obtain ⟨_, hsupport, hμE, hνE, hpos⟩ :=
    DominatedWeakSupport.interval_fixed_target (fun n => μs (α n)) μ hweak
      (fun n => hs (α n)) E hE hleak' δ hδ hmass'
  exact ⟨μ, α, hα, hweak, hdom, hsupport, hμE, hνE, hpos⟩

end Jig133.DominatedMeasureCompactness

end
end File_DominatedMeasureCompactness

section File_DominatedUniformIntervals

/-!
# Uniform interval discrepancy under dominated weak convergence

Actual cumulative masses are one-Lipschitz under domination by Lebesgue measure.
Pointwise convergence therefore becomes uniform on each compact endpoint set.
Taking two endpoints gives a bound uniform over moving closed intervals.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal UniformConvergence

noncomputable section

namespace Jig133.DominatedUniformIntervals

def cumulative (μ : FiniteMeasure ℝ) (x : ℝ) : ℝ :=
  (μ : Measure ℝ).real (Iic x)

theorem interval_difference (μ : FiniteMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (μ : Measure ℝ).real (Ioc a b) = cumulative μ b - cumulative μ a := by
  rw [← Iic_sdiff_Iic]
  exact measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic

theorem cumulative_increment (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) ≤ volume) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ cumulative μ b - cumulative μ a ∧
      cumulative μ b - cumulative μ a ≤ b - a := by
  rw [← interval_difference μ hab]
  refine ⟨measureReal_nonneg, ?_⟩
  calc
    _ ≤ volume.real (Ioc a b) := ENNReal.toReal_mono (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (hμ _)
    _ = b - a := Real.volume_real_Ioc_of_le hab

theorem cumulative_lipschitz (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) ≤ volume) : LipschitzWith 1 (cumulative μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total x y with hxy | hyx
  · have h := cumulative_increment μ hμ hxy
    rw [abs_sub_comm (cumulative μ x), abs_of_nonneg h.1,
      abs_sub_comm x, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h.2
  · have h := cumulative_increment μ hμ hyx
    rw [abs_of_nonneg h.1, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h.2

theorem closed_interval_difference (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) ≤ volume) {a b : ℝ} (hab : a ≤ b) :
    (μ : Measure ℝ).real (Icc a b) = cumulative μ b - cumulative μ a := by
  let : NullSingletonClass (μ : Measure ℝ) := ⟨fun x => by
    apply le_antisymm _ zero_le
    simpa only [measure_singleton] using hμ {x}⟩
  rw [← measureReal_congr (Ioc_ae_eq_Icc (μ := (μ : Measure ℝ)))]
  exact interval_difference μ hab

/-- Equicontinuity is proved from domination, and pointwise convergence from
the actual weak limit. Neither uniform convergence nor limit domination is an input. -/
theorem cumulative_uniform_on_compact (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≤ volume) (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformly (fun n (x : K) => cumulative (μs n) x)
      (fun x : K => cumulative μ x) atTop := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → K → ℝ := fun n x => cumulative (μs n) x
  have hlip : ∀ n, LipschitzWith 1 (F n) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (cumulative_lipschitz (μs n) ((hs n).trans hν)).dist_le_mul x y
  have heq : Equicontinuous F :=
    (LipschitzWith.uniformEquicontinuous F 1 hlip).equicontinuous
  have hp : Tendsto F atTop (𝓝 (fun x : K => cumulative μ x)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    exact DominatedWeakSupport.tendsto_measureReal ν μs μ hweak hs
      (Iic (x : ℝ)) measurableSet_Iic
  have hu := (heq.tendsto_uniformFun_iff_pi atTop
    (fun x : K => cumulative μ x)).mpr hp
  exact UniformFun.tendsto_iff_tendstoUniformly.mp hu

/-- One eventual bound works for every pair of endpoints in K, including
reversed and coincident endpoints. K itself need not be an interval. -/
theorem uniform_closed_intervals (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≤ volume) (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (K : Set ℝ) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a ∈ K, ∀ b ∈ K,
      |(μs n : Measure ℝ).real (Icc a b) - (μ : Measure ℝ).real (Icc a b)| < ε := by
  have hu := Metric.tendstoUniformly_iff.mp
    (cumulative_uniform_on_compact ν hν μs μ hweak hs K hK)
    (ε / 2) (by linarith)
  have hμ : (μ : Measure ℝ) ≤ volume :=
    (DominatedWeakSupport.limit_le ν μs μ hweak hs).trans hν
  filter_upwards [hu] with n hn
  intro a ha b hb
  by_cases hab : a ≤ b
  · rw [closed_interval_difference (μs n) ((hs n).trans hν) hab,
      closed_interval_difference μ hμ hab]
    have ha' := hn ⟨a, ha⟩
    have hb' := hn ⟨b, hb⟩
    simp only [Real.dist_eq] at ha' hb'
    have ht := abs_sub_le
      (cumulative (μs n) b - cumulative μ b) 0
      (cumulative (μs n) a - cumulative μ a)
    rw [sub_zero, zero_sub, abs_neg] at ht
    rw [abs_sub_comm (cumulative μ a)] at ha'
    rw [abs_sub_comm (cumulative μ b)] at hb'
    have heq : cumulative (μs n) b - cumulative (μs n) a -
        (cumulative μ b - cumulative μ a) =
      (cumulative (μs n) b - cumulative μ b) -
        (cumulative (μs n) a - cumulative μ a) := by ring
    rw [heq]
    linarith
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    simpa only [measureReal_empty, sub_self, abs_zero] using hε

/-- Endpoint sequences may depend arbitrarily on the index. -/
theorem moving_closed_intervals (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≤ volume) (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) (hs : ∀ n, (μs n : Measure ℝ) ≤ ν)
    (K : Set ℝ) (hK : IsCompact K) (a b : ℕ → ℝ)
    (ha : ∀ n, a n ∈ K) (hb : ∀ n, b n ∈ K) :
    Tendsto (fun n => (μs n : Measure ℝ).real (Icc (a n) (b n)) -
      (μ : Measure ℝ).real (Icc (a n) (b n))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [uniform_closed_intervals ν hν μs μ hweak hs K hK ε hε] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn (a n) (ha n) (b n) (hb n)

end Jig133.DominatedUniformIntervals

end
end File_DominatedUniformIntervals

section File_DominatedMovingTarget

/-!
# A fixed compact density target along an actual weak subsequence

Domination, vanishing leakage and eventual positive mass on the original
measurable set produce one weak subsequence and one compact positive target.
The interval lower bound is uniform in both endpoints with an additive error.
No convergence rate or relative estimate on shrinking intervals is asserted.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Jig133.DominatedMovingTarget

abbrev I : Set ℝ := Icc (-1 : ℝ) 1

/-- Convert an actual lower measure bound to real masses on measurable sets. -/
theorem real_lower_bound (μ : FiniteMeasure ℝ) (K : Set ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hKμ : ENNReal.ofReal c • volume.restrict K ≤ (μ : Measure ℝ))
    (J : Set ℝ) (hJ : MeasurableSet J) :
    c * volume.real (K ∩ J) ≤ (μ : Measure ℝ).real J := by
  have h := ENNReal.toReal_mono (measure_ne_top (μ : Measure ℝ) J) (hKμ J)
  change (ENNReal.ofReal c • volume.restrict K).real J ≤
    (μ : Measure ℝ).real J at h
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hc,
    measureReal_restrict_apply hJ, inter_comm J K] at h
  exact h

/-- Actual weak convergence gives an additive bound uniform over every pair
of interval endpoints in I, once the limit has the stated measure lower bound. -/
theorem uniform_interval_lower_bound (μs : ℕ → FiniteMeasure ℝ)
    (μ : FiniteMeasure ℝ) (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n, (μs n : Measure ℝ) ≤ volume.restrict I)
    (K : Set ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hKμ : ENNReal.ofReal c • volume.restrict K ≤ (μ : Measure ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a ∈ I, ∀ b ∈ I,
      c * volume.real (K ∩ Icc a b) - ε ≤ (μs n : Measure ℝ).real (Icc a b) := by
  filter_upwards [DominatedUniformIntervals.uniform_closed_intervals
    (volume.restrict I) Measure.restrict_le_self μs μ hweak hs I isCompact_Icc ε hε]
    with n hn
  intro a ha b hb
  have hclose := (abs_lt.mp (hn a ha b hb)).1
  have hlower := real_lower_bound μ K c hc hKμ (Icc a b) measurableSet_Icc
  linarith

/-- Construct the same limit, strictly increasing subsequence and compact
target before choosing the tolerance or interval endpoints. The original set
need only be measurable, and the original E-mass bound need only hold eventually. -/
theorem exists_compact_uniform_target (μs : ℕ → FiniteMeasure ℝ)
    (hs : ∀ n, (μs n : Measure ℝ) ≤ volume.restrict I)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun n => (μs n : Measure ℝ).real Eᶜ) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ)
    (hmass : ∀ᶠ n in atTop, δ ≤ (μs n : Measure ℝ).real E) :
    ∃ μ : FiniteMeasure ℝ, ∃ α : ℕ → ℕ, ∃ K : Set ℝ,
      StrictMono α ∧
      Tendsto (fun n => μs (α n)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ) ≤ volume.restrict I ∧
      (μ : Measure ℝ) Eᶜ = 0 ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ E) ∧
      δ ≤ (μ : Measure ℝ).real E ∧
      δ ≤ volume.real (E ∩ I) ∧
      IsCompact K ∧ K ⊆ E ∩ I ∧
      0 < volume.real K ∧ δ / 4 < volume.real K ∧
      ENNReal.ofReal (δ / 4) • volume.restrict K ≤ (μ : Measure ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ a ∈ I, ∀ b ∈ I,
        (δ / 4) * volume.real (K ∩ Icc a b) - ε ≤
          (μs (α n) : Measure ℝ).real (Icc a b) := by
  have htotal : ∀ᶠ n in atTop, δ ≤ (μs n : Measure ℝ).real univ := by
    filter_upwards [hmass] with n hn
    exact hn.trans (measureReal_mono (subset_univ E)
      (measure_ne_top (μs n : Measure ℝ) univ))
  obtain ⟨μ, α, hα, hweak, hdom, hsupport, hμE, hvolE, _hposE⟩ :=
    DominatedMeasureCompactness.exists_positive_target μs hs E hE hleak δ hδ htotal
  obtain ⟨K, hK, hKEI, hKpos, hKquarter, hKμ⟩ :=
    DominatedDensityTarget.exists_compact_density_target μ hdom E hE δ hδ hμE
  have hzero : (μ : Measure ℝ) Eᶜ = 0 := by
    simpa only [ae_iff, Set.compl_def] using hsupport
  refine ⟨μ, α, K, hα, hweak, hdom, hzero, hsupport, hμE, hvolE,
    hK, hKEI, hKpos, hKquarter, hKμ, ?_⟩
  intro ε hε
  exact uniform_interval_lower_bound (fun n => μs (α n)) μ hweak
    (fun n => hs (α n)) K (δ / 4) (div_nonneg hδ.le (by norm_num)) hKμ ε hε

end Jig133.DominatedMovingTarget

end
end File_DominatedMovingTarget

section File_RetainedIndicatorTarget

/-!
# Actual retained indicator measures and a fixed compact target

The measures are literal restrictions of volume to the given compact sets.
Vanishing leakage and eventual retained mass yield one weak subsequence and
one compact density target, before every tolerance and interval endpoint.
Only an additive interval error is asserted.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

namespace Jig133.RetainedIndicatorTarget

abbrev I : Set ℝ := Icc (-1 : ℝ) 1

def buffer (δ : ℝ) : Set ℝ := Icc (-1 + δ / 16) (1 - δ / 16)

/-- The actual measure with density one on the retained compact set. -/
def indicatorMeasure (R : Set ℝ) (hR : IsCompact R) : FiniteMeasure ℝ :=
  ⟨volume.restrict R, ⟨by
    rw [Measure.restrict_apply_univ]
    exact hR.measure_lt_top (μ := volume)⟩⟩

theorem indicatorMeasure_real_apply (R : Set ℝ) (hR : IsCompact R)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (indicatorMeasure R hR : Measure ℝ).real S = volume.real (S ∩ R) := by
  change (volume.restrict R).real S = volume.real (S ∩ R)
  exact measureReal_restrict_apply hS

theorem indicatorMeasure_real_univ (R : Set ℝ) (hR : IsCompact R) :
    (indicatorMeasure R hR : Measure ℝ).real univ = volume.real R := by
  change (volume.restrict R).real univ = volume.real R
  exact measureReal_restrict_apply_univ R

theorem indicatorMeasure_real_compl (R : Set ℝ) (hR : IsCompact R)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (indicatorMeasure R hR : Measure ℝ).real Eᶜ = volume.real (R \ E) := by
  rw [indicatorMeasure_real_apply R hR Eᶜ hE.compl]
  change volume.real (Eᶜ ∩ R) = volume.real (R ∩ Eᶜ)
  rw [inter_comm]

theorem indicatorMeasure_le (R : Set ℝ) (hR : IsCompact R) (hRI : R ⊆ I) :
    (indicatorMeasure R hR : Measure ℝ) ≤ volume.restrict I := by
  change volume.restrict R ≤ volume.restrict I
  exact Measure.restrict_mono_set volume hRI

/-- The displayed actual set leakage implies convergence of the restricted
measure's complement mass, including empty early retained sets. -/
theorem leakage_tendsto_zero (R : ℕ → Set ℝ) (hR : ∀ j, IsCompact (R j))
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : ∀ j, volume (R j \ E) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1))) :
    Tendsto (fun j => (indicatorMeasure (R j) (hR j) : Measure ℝ).real Eᶜ)
      atTop (𝓝 0) := by
  have hbound (j : ℕ) :
      (indicatorMeasure (R j) (hR j) : Measure ℝ).real Eᶜ ≤
        1 / ((j : ℝ) + 1) := by
    rw [indicatorMeasure_real_compl _ _ E hE]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleak j)
    simpa only [Measure.real, ENNReal.toReal_ofReal
      (show 0 ≤ 1 / ((j : ℝ) + 1) by positivity)] using h
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Finite mass decomposition pays an explicit δ/8 leakage margin. -/
theorem eventually_target_mass (R : ℕ → Set ℝ) (hR : ∀ j, IsCompact (R j))
    (E : Set ℝ) (hE : MeasurableSet E) (δ : ℝ) (hδ : 0 < δ)
    (hleak : Tendsto
      (fun j => (indicatorMeasure (R j) (hR j) : Measure ℝ).real Eᶜ)
      atTop (𝓝 0))
    (hmass : ∀ᶠ j in atTop, 3 * δ / 8 ≤ volume.real (R j)) :
    ∀ᶠ j in atTop, δ / 4 ≤
      (indicatorMeasure (R j) (hR j) : Measure ℝ).real E := by
  have hsmall := hleak.eventually_le_const (by positivity : (0 : ℝ) < δ / 8)
  filter_upwards [hmass, hsmall] with j hj hleakj
  have hsplit := measureReal_add_measureReal_compl
    (μ := (indicatorMeasure (R j) (hR j) : Measure ℝ)) hE
  rw [indicatorMeasure_real_univ] at hsplit
  linarith

/-- Construct the actual indicator weak subsequence and one fixed compact
target in the closed interior buffer. No abstract measure sequence, density,
weak limit, or target is supplied as a premise. -/
theorem exists_compact_target (R : ℕ → Set ℝ) (hR : ∀ j, IsCompact (R j))
    (hRI : ∀ j, R j ⊆ I) (E : Set ℝ) (hE : IsCompact E)
    (δ : ℝ) (hδ : 0 < δ) (hbuffer : ∀ j, R j ⊆ buffer δ)
    (hleak : ∀ j, volume (R j \ E) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)))
    (hmass : ∀ᶠ j in atTop, 3 * δ / 8 ≤ volume.real (R j)) :
    ∃ μ : FiniteMeasure ℝ, ∃ α : ℕ → ℕ, ∃ K : Set ℝ,
      StrictMono α ∧
      Tendsto (fun j => indicatorMeasure (R (α j)) (hR (α j))) atTop (𝓝 μ) ∧
      (μ : Measure ℝ) ≤ volume.restrict I ∧
      (μ : Measure ℝ) (E ∩ buffer δ)ᶜ = 0 ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ E ∩ buffer δ) ∧
      δ / 4 ≤ (μ : Measure ℝ).real (E ∩ buffer δ) ∧
      IsCompact K ∧ K ⊆ E ∩ buffer δ ∧
      0 < volume.real K ∧ δ / 16 < volume.real K ∧
      ENNReal.ofReal (δ / 16) • volume.restrict K ≤ (μ : Measure ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a ∈ I, ∀ b ∈ I,
        (δ / 16) * volume.real (K ∩ Icc a b) - ε ≤
          volume.real (R (α j) ∩ Icc a b) := by
  let E' := E ∩ buffer δ
  have hE' : MeasurableSet E' := hE.measurableSet.inter measurableSet_Icc
  have hdiff (j : ℕ) : R j \ E' = R j \ E := by
    ext x
    constructor
    · rintro ⟨hx, hnot⟩
      exact ⟨hx, fun hxE => hnot ⟨hxE, hbuffer j hx⟩⟩
    · rintro ⟨hx, hnot⟩
      exact ⟨hx, fun hxE' => hnot hxE'.1⟩
  have hleak' : ∀ j, volume (R j \ E') ≤
      ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    rw [hdiff j]
    exact hleak j
  have hlim := leakage_tendsto_zero R hR E' hE' hleak'
  have hmass' := eventually_target_mass R hR E' hE' δ hδ hlim hmass
  obtain ⟨μ, α, K, hα, hweak, hdom, hzero, hsupport, hμE, _hvolE,
      hK, hKE, hKpos, hKquarter, hKμ, huniform⟩ :=
    DominatedMovingTarget.exists_compact_uniform_target
      (fun j => indicatorMeasure (R j) (hR j))
      (fun j => indicatorMeasure_le (R j) (hR j) (hRI j)) E' hE' hlim
      (δ / 4) (by positivity) hmass'
  have hcoeff : δ / 4 / 4 = δ / 16 := by ring
  rw [hcoeff] at hKquarter hKμ huniform
  refine ⟨μ, α, K, hα, hweak, hdom, hzero, hsupport, hμE, hK,
    fun x hx => (hKE hx).1, hKpos, hKquarter, hKμ, ?_⟩
  intro ε hε
  filter_upwards [huniform ε hε] with j hj
  intro a ha b hb
  have h := hj a ha b hb
  rw [indicatorMeasure_real_apply _ _ _ measurableSet_Icc,
    inter_comm (Icc a b) (R (α j))] at h
  exact h

end Jig133.RetainedIndicatorTarget

end
end File_RetainedIndicatorTarget

section File_CompactWindowLimit

/-!
# Fixed compact targets from compact windows with vanishing leakage

Only finitely early unsupported windows are clipped to the interval. The
resulting lower bound is stated for the original windows, uniformly in endpoints.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Jig133.CompactWindowLimit
open RetainedIndicatorTarget

theorem exists_fixed_target (U : ℕ → Set ℝ) (hU : ∀ j, IsCompact (U j))
    (hUI : ∀ᶠ j in atTop, U j ⊆ Icc (-1 : ℝ) 1)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hleak : Tendsto (fun j => volume.real (U j \ E)) atTop (𝓝 0))
    (m : ℝ) (hm : 0 < m) (hmass : ∀ᶠ j in atTop, m ≤ volume.real (U j)) :
    ∃ α : ℕ → ℕ, ∃ K : Set ℝ, StrictMono α ∧ IsCompact K ∧
      K ⊆ E ∩ Icc (-1 : ℝ) 1 ∧ m / 8 < volume.real K ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a ∈ Icc (-1 : ℝ) 1, ∀ b ∈ Icc (-1 : ℝ) 1,
        (m / 8) * volume.real (K ∩ Icc a b) - ε ≤ volume.real (U (α j) ∩ Icc a b) := by
  let V (j : ℕ) := U j ∩ Icc (-1 : ℝ) 1
  have hV (j : ℕ) : IsCompact (V j) := (hU j).inter isCompact_Icc
  let μs (j : ℕ) := indicatorMeasure (V j) (hV j)
  have hdom (j : ℕ) : (μs j : Measure ℝ) ≤ volume.restrict (Icc (-1 : ℝ) 1) :=
    indicatorMeasure_le (V j) (hV j) inter_subset_right
  have heq : ∀ᶠ j in atTop, V j = U j := hUI.mono (fun j hj => inter_eq_left.mpr hj)
  have hlim : Tendsto (fun j => (μs j : Measure ℝ).real Eᶜ) atTop (𝓝 0) := by
    apply hleak.congr'
    filter_upwards [heq] with j hj
    rw [show (μs j : Measure ℝ).real Eᶜ = volume.real (V j \ E) from
      indicatorMeasure_real_compl (V j) (hV j) E hE, hj]
  have htotal : ∀ᶠ j in atTop, m ≤ (μs j : Measure ℝ).real univ := by
    filter_upwards [heq, hmass] with j hj hmj
    change m ≤ (indicatorMeasure (V j) (hV j) : Measure ℝ).real univ
    rw [indicatorMeasure_real_univ, hj]
    exact hmj
  have hmassE : ∀ᶠ j in atTop, m / 2 ≤ (μs j : Measure ℝ).real E := by
    filter_upwards [htotal, hlim.eventually_le_const (show (0 : ℝ) < m / 2 by positivity)]
      with j hj hsmall
    have hsplit := measureReal_add_measureReal_compl (μ := (μs j : Measure ℝ)) hE
    linarith
  obtain ⟨μ, α, K, hα, _hweak, _hdom, _hzero, _hsupport, _hμE, _hvolE,
      hK, hKE, _hKpos, hKmass, _hKμ, huniform⟩ :=
    DominatedMovingTarget.exists_compact_uniform_target μs hdom E hE hlim
      (m / 2) (by positivity) hmassE
  have he : m / 2 / 4 = m / 8 := by ring
  rw [he] at hKmass huniform
  refine ⟨α, K, hα, hK, hKE, hKmass, ?_⟩
  intro ε hε
  filter_upwards [huniform ε hε] with j hj
  intro a ha b hb
  have hl := hj a ha b hb
  have heval : (μs (α j) : Measure ℝ).real (Icc a b) = volume.real (V (α j) ∩ Icc a b) := by
    rw [show (μs (α j) : Measure ℝ).real (Icc a b) = volume.real (Icc a b ∩ V (α j)) from
      indicatorMeasure_real_apply _ _ _ measurableSet_Icc, inter_comm]
  rw [heval] at hl
  exact hl.trans (measureReal_mono
    (inter_subset_inter_left _ (show V (α j) ⊆ U (α j) from inter_subset_left))
    (measure_ne_top_of_subset inter_subset_left (hU (α j)).measure_lt_top.ne))

end Jig133.CompactWindowLimit

end
end File_CompactWindowLimit

section File_FixedBandWindowTarget

/-!
# One fixed compact target from the actual full-product band windows

R precedes delta; G precedes the row subsequence, source nets and polynomials.
The compact target and subsequence precede every tolerance and interval.
-/

noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped Topology
namespace Jig133.FixedBandWindowTarget
open BandTargetMeasure BandTargetConstants BandWindowExtraction FiniteSourceNets SparseSourceRows

theorem exists_uniform_fixed_targets
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ Icc (-1 : ℝ) 1)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (hSC : SourceCount nodes E) :
    ∃ R : ℕ → ℕ, (∀ n, 0 < R n) ∧ Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun n : ℕ => (R n : ℝ) / n) atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ G : ℝ, 0 < G ∧
        ∀ r : ℕ → ℕ, StrictMono r → ∀ Y : ℕ → Finset ℝ,
          (∀ j, IsSourceNet (rowNodes nodes (r j)) (Y j) (1 / (r j : ℝ))) →
          ∀ P : ℕ → ℝ[X], (∀ j, P j ≠ 0) → (∀ j i, (P j).eval (nodes (r j) i) = 0) →
          ∀ η T : ℝ, ∀ A : ℕ → ℝ,
          (∀ᶠ j in atTop, (P j).natDegree ≤ 2 * r j ∧
            δ ≤ volume.real (E ∩ band (P j) η T (A j))) →
          ∃ α : ℕ → ℕ, ∃ K : Set ℝ, StrictMono α ∧ IsCompact K ∧
            K ⊆ E ∩ Icc (-1 : ℝ) 1 ∧
            (FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G) / 8 < volume.real K ∧
            ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a ∈ Icc (-1 : ℝ) 1, ∀ b ∈ Icc (-1 : ℝ) 1,
              ((FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G) / 8) *
                volume.real (K ∩ Icc a b) - ε ≤
                volume.real (region E R (Y (α j)) (P (α j)) η T (A (α j)) δ G (r (α j)) ∩ Icc a b) := by
  obtain ⟨R, hpos, hmono, htop, hratio, hrows⟩ :=
    exists_uniform_windows nodes hsupp E hE hEI hSC
  refine ⟨R, hpos, hmono, htop, hratio, ?_⟩
  intro δ hδ hδ2
  obtain ⟨G, hG, hlate⟩ := hrows δ hδ hδ2
  refine ⟨G, hG, ?_⟩
  intro r hr Y hY P hP hroots η T A hband
  let U (j : ℕ) := region E R (Y j) (P j) η T (A j) δ G (r j)
  let m := FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G
  obtain ⟨hc, hB, hL, _⟩ := positive hδ G
  have hm : 0 < m := div_pos (mul_pos (FullProductBandScale.width_bounds hc hB hL).1 hδ) hG
  have hfacts : ∀ᶠ j in atTop, U j ⊆ Icc (-1 : ℝ) 1 ∧ m ≤ volume.real (U j) ∧
      volume.real (U j \ E) ≤ 1 / (R (r j) : ℝ) := by
    filter_upwards [hr.tendsto_atTop.eventually hlate, hband] with j hj hb
    have h := hj (Y j) (hY j) (P j) (hP j) (hroots j) η T (A j) hb.1 hb.2
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have htR : Tendsto (fun j => (R (r j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (htop.comp hr.tendsto_atTop)
  have hinv : Tendsto (fun j => 1 / (R (r j) : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htR
  have hleak : Tendsto (fun j => volume.real (U j \ E)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg))
      (hfacts.mono (fun _ h => h.2.2)) hinv
  exact CompactWindowLimit.exists_fixed_target U
    (fun j => region_compact E R (Y j) (P j) η T (A j) δ G (r j))
    (hfacts.mono (fun _ h => h.1)) E hE hleak m hm (hfacts.mono (fun _ h => h.2.1))

end Jig133.FixedBandWindowTarget

end
end File_FixedBandWindowTarget

end Submissions.J5P133FixedBandWindowTarget
namespace Submissions.J5P133FixedBandWindowTarget.Proof

section PublicationAlias
open Set MeasureTheory Polynomial Filter
open scoped Topology
open Jig133
open Jig133.BandTargetMeasure Jig133.BandTargetConstants Jig133.BandWindowExtraction
open Jig133.FiniteSourceNets Jig133.SparseSourceRows

theorem proof
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ Icc (-1 : ℝ) 1)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (hSC : SourceCount nodes E) :
    ∃ R : ℕ → ℕ, (∀ n, 0 < R n) ∧ Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun n : ℕ => (R n : ℝ) / n) atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ G : ℝ, 0 < G ∧
        ∀ r : ℕ → ℕ, StrictMono r → ∀ Y : ℕ → Finset ℝ,
          (∀ j, IsSourceNet (rowNodes nodes (r j)) (Y j) (1 / (r j : ℝ))) →
          ∀ P : ℕ → ℝ[X], (∀ j, P j ≠ 0) → (∀ j i, (P j).eval (nodes (r j) i) = 0) →
          ∀ η T : ℝ, ∀ A : ℕ → ℝ,
          (∀ᶠ j in atTop, (P j).natDegree ≤ 2 * r j ∧
            δ ≤ volume.real (E ∩ band (P j) η T (A j))) →
          ∃ α : ℕ → ℕ, ∃ K : Set ℝ, StrictMono α ∧ IsCompact K ∧
            K ⊆ E ∩ Icc (-1 : ℝ) 1 ∧
            (FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G) / 8 < volume.real K ∧
            ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a ∈ Icc (-1 : ℝ) 1, ∀ b ∈ Icc (-1 : ℝ) 1,
              ((FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G) / 8) *
                volume.real (K ∩ Icc a b) - ε ≤
                volume.real (region E R (Y (α j)) (P (α j)) η T (A (α j)) δ G (r (α j)) ∩ Icc a b) :=
  Jig133.FixedBandWindowTarget.exists_uniform_fixed_targets nodes hsupp E hE hEI hSC
end PublicationAlias

end Submissions.J5P133FixedBandWindowTarget.Proof
