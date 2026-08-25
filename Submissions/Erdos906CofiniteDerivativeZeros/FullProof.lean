import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Complex
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Flattened from CofiniteDerivatives/Topology.lean. -/
section

open Set

namespace CofiniteDerivatives

variable {X : Type*} [TopologicalSpace X]

/-- The set of indices whose corresponding set meets `U`. -/
def goodOrders (Z : ℕ → Set X) (U : Set X) : Set ℕ :=
  {n | (Z n ∩ U).Nonempty}

/-- Every nonempty open set is met by all sufficiently large members of `Z`. -/
def CofinitelyHits (Z : ℕ → Set X) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → ∃ N, ∀ n ≥ N, n ∈ goodOrders Z U

/-- Every strictly increasing subsequence of `Z` has dense union. -/
def EverySubsequenceDense (Z : ℕ → Set X) : Prop :=
  ∀ s : ℕ → ℕ, StrictMono s → Dense (⋃ k, Z (s k))

/-- A strictly increasing sequence of natural numbers is eventually above every bound. -/
lemma strictMono_eventually_ge {s : ℕ → ℕ} (hs : StrictMono s) (N : ℕ) :
    ∃ k, N ≤ s k := by
  exact ⟨N, hs.id_le N⟩

/-- If the bad indices are infinite, they contain a strictly increasing subsequence. -/
lemma exists_strictMono_of_not_finite {P : ℕ → Prop}
    (hP : Set.Infinite {n | P n}) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k, P (s k) := by
  apply Nat.exists_strictMono_subsequence
  intro N
  obtain ⟨n, hn, hnrange⟩ := hP.exists_notMem_finset (Finset.range (N + 1))
  simp only [Finset.mem_range, not_lt] at hnrange
  exact ⟨n, by omega, hn⟩

/-- Cofinite hitting is equivalent to density along every increasing subsequence. -/
theorem cofiniteHits_iff_everySubsequenceDense (Z : ℕ → Set X) :
    CofinitelyHits Z ↔ EverySubsequenceDense Z := by
  constructor
  · intro hcof s hs
    rw [dense_iff_inter_open]
    intro U hU hUne
    obtain ⟨N, hN⟩ := hcof U hU hUne
    obtain ⟨k, hk⟩ := strictMono_eventually_ge hs N
    have hgood : s k ∈ goodOrders Z U := hN _ hk
    rcases hgood with ⟨z, hzZ, hzU⟩
    exact ⟨z, hzU, mem_iUnion.mpr ⟨k, hzZ⟩⟩
  · intro hsub U hU hUne
    by_contra heventual
    push Not at heventual
    have hinf : Set.Infinite ((goodOrders Z U)ᶜ) := by
      apply Set.infinite_of_forall_exists_gt
      intro N
      obtain ⟨n, hNn, hn⟩ := heventual (N + 1)
      exact ⟨n, hn, lt_of_lt_of_le (Nat.lt_succ_self N) hNn⟩
    obtain ⟨s, hs, hbad⟩ := exists_strictMono_of_not_finite hinf
    have hdense := hsub s hs
    obtain ⟨z, hzU, hzUnion⟩ := hdense.inter_open_nonempty U hU hUne
    rcases mem_iUnion.mp hzUnion with ⟨k, hzZ⟩
    exact hbad k ⟨z, hzZ, hzU⟩

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/Derivatives.lean. -/
section

open Set

namespace CofiniteDerivatives

/-- The zero set of the `n`-th complex derivative. -/
def derivativeZeroSet (f : ℂ → ℂ) (n : ℕ) : Set ℂ :=
  {z | iteratedDeriv n f z = 0}

/-- Every nonempty open set contains a zero of every sufficiently high derivative. -/
def DerivativesCofinitelyHit (f : ℂ → ℂ) : Prop :=
  CofinitelyHits (derivativeZeroSet f)

/-- Along every increasing sequence of derivative orders, the union of zero sets is dense. -/
def EveryDerivativeSubsequenceDense (f : ℂ → ℂ) : Prop :=
  EverySubsequenceDense (derivativeZeroSet f)

/-- Exact quantifier equivalence for zeros of iterated complex derivatives. -/
theorem derivativesCofinitelyHit_iff_everyDerivativeSubsequenceDense (f : ℂ → ℂ) :
    DerivativesCofinitelyHit f ↔ EveryDerivativeSubsequenceDense f :=
  cofiniteHits_iff_everySubsequenceDense (derivativeZeroSet f)

/-- The cofinite formulation, expanded into its original quantifier order. -/
theorem derivativesCofinitelyHit_iff (f : ℂ → ℂ) :
    DerivativesCofinitelyHit f ↔
      ∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0 := by
  unfold DerivativesCofinitelyHit CofinitelyHits goodOrders derivativeZeroSet
  constructor
  · intro h U hU hUne
    obtain ⟨N, hN⟩ := h U hU hUne
    refine ⟨N, fun n hn ↦ ?_⟩
    rcases hN n hn with ⟨z, hz, hzU⟩
    exact ⟨z, hzU, hz⟩
  · intro h U hU hUne
    obtain ⟨N, hN⟩ := h U hU hUne
    refine ⟨N, fun n hn ↦ ?_⟩
    rcases hN n hn with ⟨z, hzU, hz⟩
    exact ⟨z, hz, hzU⟩

/-- Under cofinite hitting, only finitely many derivatives can be zero-free on any fixed
positive-radius disk. -/
theorem finite_zeroFree_derivative_orders_on_ball
    (f : ℂ → ℂ) (hf : DerivativesCofinitelyHit f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    {n : ℕ | ∀ z ∈ Metric.ball c R, iteratedDeriv n f z ≠ 0}.Finite := by
  obtain ⟨N, hN⟩ := (derivativesCofinitelyHit_iff f).mp hf
    (Metric.ball c R) Metric.isOpen_ball (Metric.nonempty_ball.mpr hR)
  apply (finite_Iio N).subset
  intro n hn
  by_contra hnN
  obtain ⟨z, hzball, hzero⟩ := hN n (Nat.le_of_not_gt hnN)
  exact hn z hzball hzero

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/DiskBasis.lean. -/
section

open Complex Function Metric Set

namespace CofiniteDerivatives

noncomputable section

/-- Rational center/radius data for disks whose radius is smaller than the center norm. -/
def RationalDiskData :=
  {q : (ℚ × ℚ) × ℚ //
    0 < q.2 ∧ (q.2 : ℝ) < ‖(q.1.1 : ℂ) + (q.1.2 : ℂ) * I‖}

instance : Countable RationalDiskData := by
  unfold RationalDiskData
  infer_instance

instance : Nonempty RationalDiskData := by
  refine ⟨⟨((1, 0), 1 / 2), ?_⟩⟩
  norm_num

/-- A fixed surjective enumeration of all admissible rational disk data. -/
noncomputable def rationalDiskEnumeration : ℕ → RationalDiskData :=
  (exists_surjective_nat RationalDiskData).choose

theorem rationalDiskEnumeration_surjective : Surjective rationalDiskEnumeration :=
  (exists_surjective_nat RationalDiskData).choose_spec

/-- The rational real coordinate of the `j`-th disk center. -/
def diskCenterRe (j : ℕ) : ℚ :=
  (rationalDiskEnumeration j).1.1.1

/-- The rational imaginary coordinate of the `j`-th disk center. -/
def diskCenterIm (j : ℕ) : ℚ :=
  (rationalDiskEnumeration j).1.1.2

/-- The positive rational radius of the `j`-th disk. -/
def diskRadiusRat (j : ℕ) : ℚ :=
  (rationalDiskEnumeration j).1.2

/-- The center of the `j`-th disk, explicitly in `ℚ + iℚ`. -/
def diskCenter (j : ℕ) : ℂ :=
  (diskCenterRe j : ℂ) + (diskCenterIm j : ℂ) * I

/-- The radius of the `j`-th disk, regarded as a real number. -/
def diskRadius (j : ℕ) : ℝ :=
  diskRadiusRat j

theorem diskCenter_eq_rational (j : ℕ) :
    diskCenter j = (diskCenterRe j : ℂ) + (diskCenterIm j : ℂ) * I :=
  rfl

theorem diskRadius_eq_rational (j : ℕ) : diskRadius j = (diskRadiusRat j : ℝ) :=
  rfl

/-- The enumerated family of admissible rational open disks. -/
def diskBasis (j : ℕ) : Set ℂ :=
  ball (diskCenter j) (diskRadius j)

theorem diskBasis_eq_ball (j : ℕ) :
    diskBasis j = ball (diskCenter j) (diskRadius j) :=
  rfl

theorem diskRadiusRat_pos (j : ℕ) : 0 < diskRadiusRat j :=
  (rationalDiskEnumeration j).2.1

theorem diskRadius_pos (j : ℕ) : 0 < diskRadius j := by
  change (0 : ℝ) < (diskRadiusRat j : ℝ)
  exact_mod_cast diskRadiusRat_pos j

theorem diskRadius_lt_norm_center (j : ℕ) : diskRadius j < ‖diskCenter j‖ :=
  (rationalDiskEnumeration j).2.2

theorem diskBasis_isOpen (j : ℕ) : IsOpen (diskBasis j) :=
  isOpen_ball

/-- Complex numbers with rational real and imaginary parts are dense in `ℂ`. -/
theorem denseRange_rationalComplex :
    DenseRange (fun q : ℚ × ℚ ↦ (q.1 : ℂ) + (q.2 : ℂ) * I) := by
  have hprod : DenseRange
      (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hcomplex := Complex.equivRealProdCLM.symm.surjective.denseRange.comp hprod
    Complex.equivRealProdCLM.symm.continuous
  simpa [Function.comp_def, Complex.equivRealProdCLM_symm_apply] using hcomplex

private theorem exists_ne_zero_mem_ball (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ≠ 0, y ∈ ball z ε := by
  by_cases hz : z = 0
  · refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · simpa using (ne_of_gt (half_pos hε))
    · rw [hz, mem_ball, dist_zero_right]
      simp only [ofReal_div, ofReal_ofNat, norm_div, norm_real, Real.norm_eq_abs, norm_ofNat,
        abs_of_pos hε]
      linarith
  · exact ⟨z, hz, mem_ball_self hε⟩

/-- Every nonempty complex open set contains one of the enumerated rational disks. -/
theorem exists_diskBasis_subset (U : Set ℂ) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ j, diskBasis j ⊆ U := by
  obtain ⟨z, hzU⟩ := hUne
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨y, hy_ne, hy_ball⟩ := exists_ne_zero_mem_ball z hε
  obtain ⟨η, hη, hη_ball⟩ := exists_ball_subset_ball hy_ball
  have hηnorm : 0 < min η ‖y‖ := lt_min hη (norm_pos_iff.mpr hy_ne)
  obtain ⟨q, hq⟩ := denseRange_rationalComplex.exists_dist_lt y hηnorm
  let c : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * I
  have hqη : dist y c < η :=
    lt_of_lt_of_le hq (min_le_left _ _)
  have hqnorm : dist y c < ‖y‖ :=
    lt_of_lt_of_le hq (min_le_right _ _)
  have hc_ne : c ≠ 0 := by
    intro hc
    rw [hc, dist_zero_right] at hqnorm
    exact (lt_irrefl _ hqnorm)
  have hcU : c ∈ U :=
    hεU (hη_ball (mem_ball'.mpr hqη))
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU c hcU
  have hρnorm : 0 < min ρ ‖c‖ := lt_min hρ (norm_pos_iff.mpr hc_ne)
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℚ, (0 : ℝ) < r ∧ (r : ℝ) < min ρ ‖c‖ :=
    exists_rat_btwn hρnorm
  let data : RationalDiskData := ⟨((q.1, q.2), r), by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hr0
    · exact lt_of_lt_of_le hr (min_le_right _ _)⟩
  obtain ⟨j, hj⟩ := rationalDiskEnumeration_surjective data
  refine ⟨j, ?_⟩
  have hcj : diskCenter j = c := by
    simp [diskCenter, diskCenterRe, diskCenterIm, c, hj, data]
  have hrj : diskRadius j = (r : ℝ) := by
    simp [diskRadius, diskRadiusRat, hj, data]
  rw [diskBasis_eq_ball, hcj, hrj]
  exact (ball_subset_ball (le_of_lt (lt_of_lt_of_le hr (min_le_left _ _)))).trans hρU

/-- A positive lower norm bound for the closed ball at half the enumerated radius. -/
def diskNormLower (j : ℕ) : ℝ :=
  ‖diskCenter j‖ - diskRadius j / 2

/-- An upper norm bound for the closed ball at half the enumerated radius. -/
def diskNormUpper (j : ℕ) : ℝ :=
  ‖diskCenter j‖ + diskRadius j / 2

theorem diskNormLower_pos (j : ℕ) : 0 < diskNormLower j := by
  have hr := diskRadius_lt_norm_center j
  have hr0 := diskRadius_pos j
  simp only [diskNormLower]
  linarith

theorem diskNormUpper_pos (j : ℕ) : 0 < diskNormUpper j := by
  have hδ := diskNormLower_pos j
  have hr0 := diskRadius_pos j
  simp only [diskNormLower, diskNormUpper] at hδ ⊢
  linarith

/-- Every point of the closed half-radius disk has norm in the explicit compact interval
`[diskNormLower j, diskNormUpper j]`. -/
theorem norm_mem_closedBall_half_bounds (j : ℕ) {z : ℂ}
    (hz : z ∈ closedBall (diskCenter j) (diskRadius j / 2)) :
    diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j := by
  have hdist : ‖z - diskCenter j‖ ≤ diskRadius j / 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hdist' : ‖diskCenter j - z‖ ≤ diskRadius j / 2 := by
    simpa only [norm_sub_rev] using hdist
  constructor
  · have htriangle := norm_le_norm_add_norm_sub' (diskCenter j) z
    simp only [diskNormLower]
    linarith
  · have htriangle := norm_le_norm_add_norm_sub (diskCenter j) z
    simp only [diskNormUpper]
    linarith

/-- The closed half-radius disk is bounded away from zero by `diskNormLower j`. -/
theorem norm_mem_closedBall_half_lower (j : ℕ) {z : ℂ}
    (hz : z ∈ closedBall (diskCenter j) (diskRadius j / 2)) :
    diskNormLower j ≤ ‖z‖ :=
  (norm_mem_closedBall_half_bounds j hz).1

/-- In particular, the closed half-radius disk does not contain zero. -/
theorem zero_not_mem_closedBall_half (j : ℕ) :
    0 ∉ closedBall (diskCenter j) (diskRadius j / 2) := by
  intro hzero
  have hlower := norm_mem_closedBall_half_lower j hzero
  have hlower' : diskNormLower j ≤ 0 := by
    simpa only [norm_zero] using hlower
  exact (not_le_of_gt (diskNormLower_pos j)) hlower'

theorem closedBall_half_isBounded (j : ℕ) :
    Bornology.IsBounded (closedBall (diskCenter j) (diskRadius j / 2)) :=
  Metric.isBounded_closedBall

/-- The boundary circle at half radius has norm between the explicit positive lower bound and
the explicit finite upper bound. -/
theorem norm_mem_sphere_half_bounds (j : ℕ) {z : ℂ}
    (hz : z ∈ sphere (diskCenter j) (diskRadius j / 2)) :
    diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j :=
  norm_mem_closedBall_half_bounds j (sphere_subset_closedBall hz)

/-- Bundled positive finite norm bounds on the boundary circle at half radius. -/
theorem exists_pos_norm_bounds_on_sphere_half (j : ℕ) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
      ∀ z ∈ sphere (diskCenter j) (diskRadius j / 2), δ ≤ ‖z‖ ∧ ‖z‖ ≤ R :=
  ⟨diskNormLower j, diskNormUpper j, diskNormLower_pos j, diskNormUpper_pos j,
    fun _ hz ↦ norm_mem_sphere_half_bounds j hz⟩

/-- The same bounds hold on the topological boundary of the open half-radius disk. -/
theorem norm_mem_frontier_ball_half_bounds (j : ℕ) {z : ℂ}
    (hz : z ∈ frontier (ball (diskCenter j) (diskRadius j / 2))) :
    diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j :=
  norm_mem_sphere_half_bounds j (frontier_ball_subset_sphere hz)

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/BorelCantelli.lean. -/
section

open Filter MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
variable (μ : Measure Ω)

/-- Summable failure probabilities imply eventual success for each target, simultaneously for a
countable family of targets. No independence assumption is used. -/
theorem ae_forall_eventually_not_failure (failure : ι → ℕ → Set Ω)
    (hsum : ∀ i, (∑' n, μ (failure i n)) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i, ∃ N, ∀ n ≥ N, ω ∉ failure i n := by
  rw [ae_all_iff]
  intro i
  have hbc : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ failure i n :=
    ae_eventually_notMem (hsum i)
  filter_upwards [hbc] with ω hω
  exact eventually_atTop.mp hω

/-- A point satisfying every eventual-success condition exists whenever the ambient measure is
nonzero. This is the deterministic-sample extraction used at the end of the proof. -/
theorem exists_forall_eventually_not_failure [NeZero μ] (failure : ι → ℕ → Set Ω)
    (hsum : ∀ i, (∑' n, μ (failure i n)) ≠ ∞) :
    ∃ ω, ∀ i, ∃ N, ∀ n ≥ N, ω ∉ failure i n := by
  have h := ae_forall_eventually_not_failure μ failure hsum
  exact Filter.Eventually.exists h

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/Extraction.lean. -/
section

open MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]

/-- The event that the `n`-th random set misses the `j`-th basic open set. -/
def holeEvent (Z : Ω → ℕ → Set X) (B : ℕ → Set X) (j n : ℕ) : Set Ω :=
  {ω | ¬(Z ω n ∩ B j).Nonempty}

/-- Summable hole probabilities on a countable inner base produce one deterministic sample whose
sets hit every nonempty open set cofinitely often. This is the complete probabilistic-to-topological
interface; it uses no independence assumptions. -/
theorem exists_cofinitelyHits_of_summable_holes
    (μ : Measure Ω) [NeZero μ]
    (Z : Ω → ℕ → Set X) (B : ℕ → Set X)
    (hB : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ j, B j ⊆ U)
    (hsum : ∀ j, (∑' n, μ (holeEvent Z B j n)) ≠ ∞) :
    ∃ ω, CofinitelyHits (Z ω) := by
  classical
  obtain ⟨ω, hω⟩ := exists_forall_eventually_not_failure μ (holeEvent Z B) hsum
  refine ⟨ω, fun U hU hUne ↦ ?_⟩
  obtain ⟨j, hjU⟩ := hB U hU hUne
  obtain ⟨N, hN⟩ := hω j
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnotHole := hN n hn
  simp only [holeEvent, mem_setOf_eq, not_not] at hnotHole
  rcases hnotHole with ⟨z, hzZ, hzB⟩
  exact ⟨z, hzZ, hjU hzB⟩

/-- The same extraction, immediately converted to density along every increasing subsequence. -/
theorem exists_everySubsequenceDense_of_summable_holes
    (μ : Measure Ω) [NeZero μ]
    (Z : Ω → ℕ → Set X) (B : ℕ → Set X)
    (hB : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ j, B j ⊆ U)
    (hsum : ∀ j, (∑' n, μ (holeEvent Z B j n)) ≠ ∞) :
    ∃ ω, EverySubsequenceDense (Z ω) := by
  obtain ⟨ω, hω⟩ := exists_cofinitelyHits_of_summable_holes μ Z B hB hsum
  exact ⟨ω, (cofiniteHits_iff_everySubsequenceDense (Z ω)).mp hω⟩

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/UniformDisk.lean. -/
section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace CofiniteDerivatives

noncomputable section

/-- Lebesgue volume restricted to the closed unit disk, regarded as a finite measure. -/
def uniformDiskFinite : FiniteMeasure ℂ where
  val := volume.restrict (closedBall 0 1)
  property := by
    constructor
    rw [Measure.restrict_apply_univ, Complex.volume_closedBall]
    simp

/-- The normalized uniform probability measure on the closed unit disk in `ℂ`. -/
def uniformDisk : Measure ℂ :=
  (uniformDiskFinite.normalize : Measure ℂ)

@[simp]
theorem uniformDiskFinite_mass : uniformDiskFinite.mass = NNReal.pi := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  simp [uniformDiskFinite, Complex.volume_closedBall]

theorem uniformDiskFinite_ne_zero : uniformDiskFinite ≠ 0 := by
  apply uniformDiskFinite.mass_nonzero_iff.mp
  rw [uniformDiskFinite_mass]
  exact NNReal.pi_ne_zero

instance uniformDisk.isProbabilityMeasure : IsProbabilityMeasure uniformDisk := by
  unfold uniformDisk
  infer_instance

theorem uniformDisk_isProbabilityMeasure : IsProbabilityMeasure uniformDisk := inferInstance

theorem uniformDisk_ne_zero : uniformDisk ≠ 0 :=
  IsProbabilityMeasure.ne_zero uniformDisk

theorem uniformDisk_ae_mem_closedBall :
    ∀ᵐ z ∂uniformDisk, z ∈ closedBall (0 : ℂ) 1 := by
  rw [ae_iff]
  change uniformDisk ((closedBall (0 : ℂ) 1)ᶜ) = 0
  unfold uniformDisk
  rw [uniformDiskFinite.toMeasure_normalize_eq_of_nonzero uniformDiskFinite_ne_zero]
  rw [Measure.coe_nnreal_smul_apply]
  rw [ENNReal.coe_inv (uniformDiskFinite.mass_nonzero_iff.mpr uniformDiskFinite_ne_zero)]
  change (uniformDiskFinite.mass⁻¹ : ℝ≥0∞) *
    (volume.restrict (closedBall (0 : ℂ) 1)) ((closedBall 0 1)ᶜ) = 0
  rw [Measure.restrict_apply' measurableSet_closedBall]
  simp

theorem uniformDisk_singleton (z : ℂ) : uniformDisk ({z} : Set ℂ) = 0 := by
  unfold uniformDisk
  rw [uniformDiskFinite.toMeasure_normalize_eq_of_nonzero uniformDiskFinite_ne_zero]
  rw [Measure.coe_nnreal_smul_apply]
  rw [ENNReal.coe_inv (uniformDiskFinite.mass_nonzero_iff.mpr uniformDiskFinite_ne_zero)]
  change (uniformDiskFinite.mass⁻¹ : ℝ≥0∞) *
    (volume.restrict (closedBall (0 : ℂ) 1)) {z} = 0
  rw [Measure.restrict_apply (measurableSet_singleton z)]
  have hsingleton : volume ({z} : Set ℂ) = 0 := by
    simp
  rw [measure_mono_null inter_subset_left hsingleton, mul_zero]

/-- The normalized disk measure is bounded by Lebesgue volume divided by `π`. -/
theorem uniformDisk_le_normalized_volume (s : Set ℂ) :
    uniformDisk s ≤ (NNReal.pi : ℝ≥0∞)⁻¹ * volume s := by
  unfold uniformDisk
  rw [uniformDiskFinite.toMeasure_normalize_eq_of_nonzero uniformDiskFinite_ne_zero]
  rw [Measure.coe_nnreal_smul_apply]
  rw [ENNReal.coe_inv (uniformDiskFinite.mass_nonzero_iff.mpr uniformDiskFinite_ne_zero)]
  change (uniformDiskFinite.mass⁻¹ : ℝ≥0∞) *
    (volume.restrict (closedBall (0 : ℂ) 1)) s ≤ (NNReal.pi : ℝ≥0∞)⁻¹ * volume s
  rw [uniformDiskFinite_mass]
  simpa only [mul_comm] using
    mul_le_mul_left (Measure.restrict_le_self (μ := volume) (s := closedBall (0 : ℂ) 1) s)
      (NNReal.pi : ℝ≥0∞)⁻¹

/-- Affine small-ball bound for the normalized uniform measure on the unit disk. -/
theorem uniformDisk_affine_smallBall {a : ℂ} (ha : a ≠ 0) (w : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    uniformDisk {z | ‖a * z + w‖ < ε} ≤ ENNReal.ofReal ((ε / ‖a‖) ^ 2) := by
  let c : ℂ := -(a⁻¹ * w)
  let r : ℝ := ε / ‖a‖
  have hr : 0 ≤ r := div_nonneg hε (norm_nonneg a)
  have hsubset : {z : ℂ | ‖a * z + w‖ < ε} ⊆ ball c r := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    have hid : z - c = a⁻¹ * (a * z + w) := by
      dsimp [c]
      field_simp [ha]
      simp [sub_eq_add_neg, add_comm]
    rw [hid, norm_mul, norm_inv]
    rw [← div_eq_inv_mul]
    exact (div_lt_div_iff_of_pos_right (norm_pos_iff.mpr ha)).2 hz
  calc
    uniformDisk {z | ‖a * z + w‖ < ε} ≤ uniformDisk (ball c r) :=
      measure_mono hsubset
    _ ≤ (NNReal.pi : ℝ≥0∞)⁻¹ * volume (ball c r) :=
      uniformDisk_le_normalized_volume _
    _ = ENNReal.ofReal ((ε / ‖a‖) ^ 2) := by
      rw [Complex.volume_ball]
      simp only [r, ENNReal.ofReal_pow hr]
      rw [mul_comm (ENNReal.ofReal (ε / ‖a‖) ^ 2) (NNReal.pi : ℝ≥0∞)]
      exact ENNReal.inv_mul_cancel_left (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero)
        ENNReal.coe_ne_top

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/Saddle.lean. -/
section

open Finset Real

namespace CofiniteDerivatives

/-- The coefficient `sqrt ((n + m)!) / m! * r^m` for the case `beta = 1 / 2`. -/
noncomputable def saddleCoeff (n m : ℕ) (r : ℝ) : ℝ :=
  √(Nat.factorial (n + m) : ℝ) / (Nat.factorial m : ℝ) * r ^ m

/-- `saddleCoeff` after removing the common factor `sqrt (n!)`. -/
noncomputable def normalizedSaddleCoeff (n m : ℕ) (r : ℝ) : ℝ :=
  √((n + 1).ascFactorial m : ℝ) / (Nat.factorial m : ℝ) * r ^ m

/-- The sum of the normalized saddle coefficients. -/
noncomputable def normalizedSaddleSeries (n : ℕ) (r : ℝ) : ℝ :=
  ∑' m : ℕ, normalizedSaddleCoeff n m r

/-- The full series of coefficients `sqrt ((n + m)!) / m! * r^m`. -/
noncomputable def saddleSeries (n : ℕ) (r : ℝ) : ℝ :=
  ∑' m : ℕ, saddleCoeff n m r

theorem saddleCoeff_eq_sqrt_factorial_mul_normalized (n m : ℕ) (r : ℝ) :
    saddleCoeff n m r = √(Nat.factorial n : ℝ) * normalizedSaddleCoeff n m r := by
  have hsqrt :
      √(Nat.factorial (n + m) : ℝ) =
        √(Nat.factorial n : ℝ) * √((n + 1).ascFactorial m : ℝ) := by
    rw [← Real.sqrt_mul (by positivity), ← Nat.cast_mul,
      Nat.factorial_mul_ascFactorial]
  rw [saddleCoeff, normalizedSaddleCoeff, hsqrt]
  ring

theorem saddleSeries_eq_sqrt_factorial_mul_normalized (n : ℕ) (r : ℝ) :
  saddleSeries n r = √(Nat.factorial n : ℝ) * normalizedSaddleSeries n r := by
  rw [saddleSeries, normalizedSaddleSeries, ← tsum_mul_left]
  exact tsum_congr fun m ↦ saddleCoeff_eq_sqrt_factorial_mul_normalized n m r

private theorem sqrt_pow_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    ∀ m : ℕ, √(x ^ m) = √x ^ m
  | 0 => by simp
  | m + 1 => by
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx m), sqrt_pow_of_nonneg x hx m,
        pow_succ]

/-- Each normalized coefficient dominates the corresponding Poisson term with parameter
`r * sqrt n`. -/
theorem poissonTerm_le_normalizedSaddleCoeff (n m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
  (r * √(n : ℝ)) ^ m / (Nat.factorial m : ℝ) ≤ normalizedSaddleCoeff n m r := by
  have hnat : n ^ m ≤ (n + 1).ascFactorial m :=
    (Nat.pow_le_pow_left (Nat.le_succ n) m).trans
      (Nat.pow_succ_le_ascFactorial (n + 1) m)
  have hcast : (n : ℝ) ^ m ≤ ((n + 1).ascFactorial m : ℝ) := by
    exact_mod_cast hnat
  have hsqrt : √((n : ℝ) ^ m) ≤ √((n + 1).ascFactorial m : ℝ) :=
    Real.sqrt_le_sqrt hcast
  calc
    (r * √(n : ℝ)) ^ m / (Nat.factorial m : ℝ) =
        r ^ m * √((n : ℝ) ^ m) / (Nat.factorial m : ℝ) := by
      rw [mul_pow, sqrt_pow_of_nonneg (n : ℝ) (by positivity)]
    _ ≤ r ^ m * √((n + 1).ascFactorial m : ℝ) / (Nat.factorial m : ℝ) := by
      gcongr
    _ = normalizedSaddleCoeff n m r := by
      rw [normalizedSaddleCoeff]
      ring

/-- A coarse global upper Stirling bound, with the correct logarithmic error. -/
theorem log_factorial_le_coarse_stirling {m : ℕ} (hm : m ≠ 0) :
  Real.log (Nat.factorial m : ℝ) ≤
      (m : ℝ) * Real.log m - m + Real.log m / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero hm
  have hseq : Real.log (Stirling.stirlingSeq (k + 1)) ≤
      Real.log (Stirling.stirlingSeq 1) :=
    Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one] at hseq
  have hlog_mul : Real.log (2 * (k + 1 : ℝ)) =
      Real.log 2 + Real.log (k + 1 : ℝ) := by
    rw [Real.log_mul] <;> positivity
  have hlog_inner : Real.log ((k + 1 : ℝ) / Real.exp 1) =
      Real.log (k + 1 : ℝ) - 1 := by
    rw [Real.log_div, Real.log_exp] <;> positivity
  have hlog_rhs : Real.log (Real.exp 1 / √2) = 1 - Real.log 2 / 2 := by
    rw [Real.log_div, Real.log_exp, Real.log_sqrt] <;> positivity
  push_cast at hseq ⊢
  rw [hlog_mul, hlog_inner, hlog_rhs] at hseq
  ring_nf at hseq ⊢
  linarith

/-- Binomial form of the normalized coefficient. -/
theorem normalizedSaddleCoeff_eq_sqrt_choose_div (n m : ℕ) (r : ℝ) :
    normalizedSaddleCoeff n m r =
  √(((n + m).choose n : ℝ) / (Nat.factorial m : ℝ)) * r ^ m := by
  rw [normalizedSaddleCoeff, Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, Real.sqrt_mul (by positivity), ← Nat.choose_symm_add,
    Real.sqrt_div (by positivity)]
  have hsqrt : 0 < √(Nat.factorial m : ℝ) := by positivity
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- At `m = floor (r * sqrt n)`, the logarithm of the normalized coefficient has leading term
`r * sqrt n`, with an explicit logarithmic loss. The hypotheses hold eventually when `r` ranges
in a fixed compact subset of `(0, ∞)`. -/
theorem log_normalizedSaddleCoeff_floor_lower (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hx : 1 ≤ r * √(n : ℝ)) (hrn : r ≤ √(n : ℝ)) :
    r * √(n : ℝ) - 2 - Real.log n / 2 ≤
      Real.log (normalizedSaddleCoeff n ⌊r * √(n : ℝ)⌋₊ r) := by
  let x : ℝ := r * √(n : ℝ)
  let m : ℕ := ⌊x⌋₊
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have hm_pos : 0 < m := (Nat.floor_pos).2 hx
  have hm_ne : m ≠ 0 := hm_pos.ne'
  have hm_le_x : (m : ℝ) ≤ x := Nat.floor_le hx_pos.le
  have hx_sub_one_lt_m : x - 1 < (m : ℝ) := Nat.sub_one_lt_floor x
  have hx_le_n : x ≤ (n : ℝ) := by
    calc
      x = r * √(n : ℝ) := rfl
      _ ≤ √(n : ℝ) * √(n : ℝ) := by gcongr
      _ = n := Real.mul_self_sqrt (by positivity)
  have hm_le_n : (m : ℝ) ≤ (n : ℝ) := hm_le_x.trans hx_le_n
  have hlog_m_le_x : Real.log m ≤ Real.log x :=
    Real.log_le_log (by positivity) hm_le_x
  have hlog_m_le_n : Real.log m ≤ Real.log n :=
    Real.log_le_log (by positivity) hm_le_n
  have hmul_log : (m : ℝ) * Real.log m ≤ (m : ℝ) * Real.log x := by
    gcongr
  have hfactorial := log_factorial_le_coarse_stirling hm_ne
  have hcoeff := poissonTerm_le_normalizedSaddleCoeff n m hr
  have hpoisson_pos : 0 < x ^ m / (Nat.factorial m : ℝ) := by positivity
  have hlog_coeff := Real.log_le_log hpoisson_pos (by simpa [x, m] using hcoeff)
  rw [Real.log_div (pow_ne_zero _ hx_pos.ne') (by positivity), Real.log_pow] at hlog_coeff
  dsimp only [x, m] at hlog_coeff ⊢
  linarith

/-- Cauchy--Schwarz majorant for the full normalized series. The first square-root factor is a
negative-binomial series and the second is an exponential series. -/
theorem normalizedSaddleSeries_summable_and_le_cauchySchwarz (n : ℕ) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 < t) (ht1 : t < 1) :
    Summable (fun m : ℕ ↦ normalizedSaddleCoeff n m r) ∧
      normalizedSaddleSeries n r ≤
        √((1 / (1 - t)) ^ (n + 1)) * √(Real.exp (r ^ 2 / t)) := by
  let A : ℕ → ℝ := fun m ↦ ((n + m).choose n : ℝ) * t ^ m
  let B : ℕ → ℝ := fun m ↦ (r ^ 2 / t) ^ m / (Nat.factorial m : ℝ)
  let f : ℕ → ℝ := fun m ↦ √(A m)
  let g : ℕ → ℝ := fun m ↦ √(B m)
  have hA_nonneg (m : ℕ) : 0 ≤ A m := by
    dsimp only [A]
    positivity
  have hB_nonneg (m : ℕ) : 0 ≤ B m := by
    dsimp only [B]
    positivity
  have ht_norm : ‖t‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos ht] using ht1
  have hA_sum : HasSum A ((1 / (1 - t)) ^ (n + 1)) := by
    simpa only [A, Nat.add_comm, one_div, inv_pow] using
      (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) n ht_norm)
  have hB_sum : HasSum B (Real.exp (r ^ 2 / t)) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa only [B] using (NormedSpace.expSeries_div_hasSum_exp (r ^ 2 / t : ℝ))
  have hf_sq (m : ℕ) : f m ^ (2 : ℝ) = A m := by
    rw [Real.rpow_two]
    exact Real.sq_sqrt (hA_nonneg m)
  have hg_sq (m : ℕ) : g m ^ (2 : ℝ) = B m := by
    rw [Real.rpow_two]
    exact Real.sq_sqrt (hB_nonneg m)
  have hf_sum : Summable (fun m ↦ f m ^ (2 : ℝ)) :=
    hA_sum.summable.congr fun m ↦ (hf_sq m).symm
  have hg_sum : Summable (fun m ↦ g m ^ (2 : ℝ)) :=
    hB_sum.summable.congr fun m ↦ (hg_sq m).symm
  have hcoeff (m : ℕ) : normalizedSaddleCoeff n m r = f m * g m := by
    have hleft : 0 ≤ normalizedSaddleCoeff n m r := by
      rw [normalizedSaddleCoeff]
      positivity
    have hright : 0 ≤ f m * g m := by
      dsimp only [f, g]
      positivity
    have hsquare : (normalizedSaddleCoeff n m r) ^ 2 = (f m * g m) ^ 2 := by
      rw [normalizedSaddleCoeff_eq_sqrt_choose_div, mul_pow,
        Real.sq_sqrt (div_nonneg (by positivity) (by positivity)), mul_pow]
      change (((n + m).choose n : ℝ) / (Nat.factorial m : ℝ)) * (r ^ m) ^ 2 =
        (√(A m)) ^ 2 * (√(B m)) ^ 2
      rw [Real.sq_sqrt (hA_nonneg m), Real.sq_sqrt (hB_nonneg m)]
      dsimp only [A, B]
      rw [div_pow]
      field_simp [ht.ne', pow_ne_zero m ht.ne']
      simp only [← pow_mul, Nat.mul_comm]
    nlinarith
  have hf_tsum : ∑' m, f m ^ (2 : ℝ) = (1 / (1 - t)) ^ (n + 1) :=
    (tsum_congr hf_sq).trans hA_sum.tsum_eq
  have hg_tsum : ∑' m, g m ^ (2 : ℝ) = Real.exp (r ^ 2 / t) :=
    (tsum_congr hg_sq).trans hB_sum.tsum_eq
  have hcs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    (fun m ↦ Real.sqrt_nonneg (A m)) (fun m ↦ Real.sqrt_nonneg (B m)) hf_sum hg_sum
  have hfg_sum : Summable (fun m ↦ f m * g m) := by
    exact (hf_sum.add hg_sum).of_nonneg_of_le
      (fun m ↦ mul_nonneg (Real.sqrt_nonneg (A m)) (Real.sqrt_nonneg (B m)))
      (fun m ↦ by
        have hmul : 0 ≤ f m * g m :=
          mul_nonneg (Real.sqrt_nonneg (A m)) (Real.sqrt_nonneg (B m))
        have htwo : 2 * (f m * g m) ≤ f m ^ (2 : ℝ) + g m ^ (2 : ℝ) := by
          simpa only [Real.rpow_two, mul_assoc] using two_mul_le_add_sq (f m) (g m)
        exact (by linarith only [hmul] : f m * g m ≤ 2 * (f m * g m)).trans htwo)
  constructor
  · exact hfg_sum.congr fun m ↦ (hcoeff m).symm
  · calc
      normalizedSaddleSeries n r = ∑' m, f m * g m := by
        rw [normalizedSaddleSeries]
        exact tsum_congr hcoeff
      _ ≤ (∑' m, f m ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' m, g m ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hcs
      _ = √((1 / (1 - t)) ^ (n + 1)) * √(Real.exp (r ^ 2 / t)) := by
        rw [hf_tsum, hg_tsum]
        simp only [Real.sqrt_eq_rpow]

/-- Explicit saddle upper bound. On `0 ≤ r ≤ R`, its correction is at most
`(R + R^2) / 2`, uniformly in `n`. -/
theorem normalizedSaddleSeries_le_exp (n : ℕ) {r : ℝ} (hn : n ≠ 0) (hr : 0 ≤ r) :
    normalizedSaddleSeries n r ≤
      Real.exp (r * √(n : ℝ) + (r + r ^ 2) / 2) := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [normalizedSaddleSeries, tsum_eq_single 0]
    · simp [normalizedSaddleCoeff]
    · intro m hm
      simp [normalizedSaddleCoeff, hm]
  let s : ℝ := √(n : ℝ)
  let u : ℝ := r / s
  let t : ℝ := r / (r + s)
  have hs : 0 < s := by
    dsimp only [s]
    positivity
  have hs_one : 1 ≤ s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hu : 0 < u := div_pos hr hs
  have ht : 0 < t := div_pos hr (add_pos hr hs)
  have ht1 : t < 1 := by
    rw [div_lt_one (add_pos hr hs)]
    linarith
  have hone : 1 / (1 - t) = 1 + u := by
    dsimp only [t, u]
    field_simp [hs.ne', hr.ne']
    ring
  have htwo : r ^ 2 / t = r * (r + s) := by
    dsimp only [t]
    field_simp [hr.ne', (add_pos hr hs).ne']
  have hseries :=
    (normalizedSaddleSeries_summable_and_le_cauchySchwarz n hr.le ht ht1).2
  rw [hone, htwo] at hseries
  refine hseries.trans ?_
  have hbase_pos : 0 < (1 + u) ^ (n + 1) := by positivity
  have hprod_pos :
      0 < √((1 + u) ^ (n + 1)) * √(Real.exp (r * (r + s))) := by
    positivity
  apply (Real.log_le_iff_le_exp hprod_pos).1
  have hlogu : Real.log (1 + u) ≤ u := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + u by positivity)
  have hs_sq : s ^ 2 = (n : ℝ) := by
    dsimp only [s]
    exact Real.sq_sqrt (by positivity)
  have hnu : ((n : ℝ) + 1) * u = r * s + u := by
    dsimp only [u]
    field_simp [hs.ne']
    nlinarith
  have hu_le_r : u ≤ r := by
    dsimp only [u]
    rw [div_le_iff₀ hs]
    nlinarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt hbase_pos.le,
    Real.log_pow, Real.log_sqrt (Real.exp_pos _).le, Real.log_exp]
  push_cast
  have hfirst : ((n : ℝ) + 1) * Real.log (1 + u) / 2 ≤
      r * s / 2 + r / 2 := by
    calc
      ((n : ℝ) + 1) * Real.log (1 + u) / 2 ≤
          ((n : ℝ) + 1) * u / 2 := by gcongr
      _ ≤ r * s / 2 + r / 2 := by linarith
  dsimp only [s] at hfirst ⊢
  nlinarith

theorem normalizedSaddleSeries_summable (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun m : ℕ ↦ normalizedSaddleCoeff n m r) :=
  (normalizedSaddleSeries_summable_and_le_cauchySchwarz n hr (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)).1

theorem normalizedSaddleSeries_pos (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 < normalizedSaddleSeries n r := by
  have hsum := normalizedSaddleSeries_summable n hr
  have hle : normalizedSaddleCoeff n 0 r ≤ normalizedSaddleSeries n r := by
    rw [normalizedSaddleSeries]
    simpa using hsum.sum_le_tsum ({0} : Finset ℕ) (fun m _ ↦ by
      rw [normalizedSaddleCoeff]
      positivity)
  have hzero : normalizedSaddleCoeff n 0 r = 1 := by
    rw [normalizedSaddleCoeff]
    simp
  rw [hzero] at hle
  exact zero_lt_one.trans_le hle

/-- The requested floor-witness lower bound in terms of the original coefficient. Equivalently,
after subtracting `log (n!) / 2`, the lower bound is `r * sqrt n - O(log n)`. -/
theorem log_saddleCoeff_floor_lower (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hx : 1 ≤ r * √(n : ℝ)) (hrn : r ≤ √(n : ℝ)) :
    Real.log (Nat.factorial n : ℝ) / 2 + r * √(n : ℝ) - 2 - Real.log n / 2 ≤
      Real.log (saddleCoeff n ⌊r * √(n : ℝ)⌋₊ r) := by
  have hr_pos : 0 < r := hr.lt_of_ne fun h ↦ by
    subst r
    norm_num at hx
  have hnormalized := log_normalizedSaddleCoeff_floor_lower n hr hx hrn
  rw [saddleCoeff_eq_sqrt_factorial_mul_normalized,
    Real.log_mul (by positivity) (by
      rw [normalizedSaddleCoeff]
      positivity), Real.log_sqrt (by positivity)]
  linarith

/-- Logarithmic upper saddle estimate for the normalized full series. -/
theorem log_normalizedSaddleSeries_le (n : ℕ) {r : ℝ} (hn : n ≠ 0) (hr : 0 ≤ r) :
    Real.log (normalizedSaddleSeries n r) ≤
      r * √(n : ℝ) + (r + r ^ 2) / 2 := by
  have hpos := normalizedSaddleSeries_pos n hr
  have hlog := Real.log_le_log hpos (normalizedSaddleSeries_le_exp n hn hr)
  simpa using hlog

/-- Logarithmic upper saddle estimate for the original full series. -/
theorem log_saddleSeries_le (n : ℕ) {r : ℝ} (hn : n ≠ 0) (hr : 0 ≤ r) :
    Real.log (saddleSeries n r) ≤
  Real.log (Nat.factorial n : ℝ) / 2 + r * √(n : ℝ) + (r + r ^ 2) / 2 := by
  rw [saddleSeries_eq_sqrt_factorial_mul_normalized,
    Real.log_mul (by positivity) (normalizedSaddleSeries_pos n hr).ne',
    Real.log_sqrt (by positivity)]
  linarith [log_normalizedSaddleSeries_le n hn hr]

/-- Uniform version of the upper estimate on a fixed compact interval `0 ≤ r ≤ R`. -/
theorem log_saddleSeries_le_on_compact (n : ℕ) {r R : ℝ} (hn : n ≠ 0)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    Real.log (saddleSeries n r) ≤
  Real.log (Nat.factorial n : ℝ) / 2 + r * √(n : ℝ) + (R + R ^ 2) / 2 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hcorrection : r + r ^ 2 ≤ R + R ^ 2 := by
    nlinarith [sq_nonneg (R - r)]
  linarith [log_saddleSeries_le n hn hr]

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/FockSeries.lean. -/
section


/-!
# The beta = 1/2 Fock series

This file studies the scalar Fock series with coefficients normalized by `sqrt (k!)`.
-/

@[expose] public section

open Filter
open scoped ENNReal NNReal Polynomial Topology

namespace CofiniteDerivatives

noncomputable section

/-- The parameter in the Fock normalization used here. -/
def fockBeta : ℝ := 1 / 2

/-- The denominator in degree `k` for the `beta = 1/2` Fock normalization. -/
def fockDenominator (k : ℕ) : ℝ :=
  Real.sqrt (k.factorial : ℝ)

/-- The normalized coefficient of a Fock series. -/
def fockCoefficient (ξ : ℕ → ℂ) (k : ℕ) : ℂ :=
  ξ k / fockDenominator k

/-- The formal multilinear series associated to the normalized coefficients. -/
def fockPowerSeries (ξ : ℕ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fockCoefficient ξ)

/-- The `beta = 1/2` Fock series. -/
def fockFunction (ξ : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, ξ k * z ^ k / fockDenominator k

theorem fockDenominator_pos (k : ℕ) : 0 < fockDenominator k := by
  simp only [fockDenominator]
  positivity

@[simp]
theorem fockDenominator_ne_zero (k : ℕ) : fockDenominator k ≠ 0 :=
  (fockDenominator_pos k).ne'

theorem fockFunction_eq_series_sum (ξ : ℕ → ℂ) :
    fockFunction ξ = (fockPowerSeries ξ).sum := by
  funext z
  rw [fockFunction, fockPowerSeries, FormalMultilinearSeries.sum]
  apply tsum_congr
  intro k
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  change ξ k * z ^ k / (fockDenominator k : ℂ) =
    (ξ k / (fockDenominator k : ℂ)) * z ^ k
  ring

private theorem summable_pow_div_sqrt_factorial (r : ℝ≥0) :
    Summable fun k : ℕ => (r : ℝ) ^ k / fockDenominator k := by
  by_cases hr : r = 0
  · subst r
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  · apply summable_of_ratio_test_tendsto_lt_one zero_lt_one
    · exact Eventually.of_forall fun k => by
        exact div_ne_zero (pow_ne_zero k (NNReal.coe_ne_zero.mpr hr))
          (fockDenominator_ne_zero k)
    · convert (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_div_atTop (r : ℝ)
          using 1
      funext k
      simp only [norm_div, Real.norm_eq_abs, abs_pow, abs_of_nonneg r.coe_nonneg,
        abs_of_pos (fockDenominator_pos k), abs_of_pos (fockDenominator_pos (k + 1)),
        Function.comp_apply]
      rw [fockDenominator, fockDenominator, Nat.factorial_succ]
      push_cast
      rw [Real.sqrt_mul (by positivity)]
      field_simp [pow_succ, NNReal.coe_ne_zero.mpr hr]
      simp [pow_succ]

/-- The Fock formal power series has infinite radius of convergence. -/
theorem fockPowerSeries_radius (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    (fockPowerSeries ξ).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg k)) (fun k => ?_)
    (summable_pow_div_sqrt_factorial r)
  rw [fockPowerSeries, FormalMultilinearSeries.ofScalars_norm, fockCoefficient, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (fockDenominator_pos k)]
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hξ k) (fockDenominator_pos k).le)
      (pow_nonneg r.coe_nonneg k)

/-- The defining formal series represents the Fock function on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    HasFPowerSeriesOnBall (fockFunction ξ) (fockPowerSeries ξ) 0 ⊤ := by
  rw [fockFunction_eq_series_sum]
  have hr : 0 < (fockPowerSeries ξ).radius := by
    rw [fockPowerSeries_radius ξ hξ]
    exact WithTop.top_pos
  simpa [fockPowerSeries_radius ξ hξ] using
    (fockPowerSeries ξ).hasFPowerSeriesOnBall hr

/-- A bounded-coefficient Fock series is analytic at every complex point. -/
theorem analyticAt_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    AnalyticAt ℂ (fockFunction ξ) z := by
  exact (hasFPowerSeriesOnBall_fockFunction ξ hξ).analyticAt_of_mem (by simp)

/-- A bounded-coefficient Fock series is entire. -/
theorem analyticOnNhd_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    AnalyticOnNhd ℂ (fockFunction ξ) Set.univ := by
  intro z _
  exact analyticAt_fockFunction ξ hξ z

/-- A bounded-coefficient Fock series is complex differentiable everywhere. -/
theorem differentiable_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    Differentiable ℂ (fockFunction ξ) := by
  intro z
  exact (analyticAt_fockFunction ξ hξ z).differentiableAt

/-- The scalar coefficients of the first derivative of a Fock series. -/
def fockDerivativeCoefficient (ξ : ℕ → ℂ) (m : ℕ) : ℂ :=
  (m + 1) * fockCoefficient ξ (m + 1)

theorem fockDerivativeCoefficient_eq_factorial (ξ : ℕ → ℂ) (m : ℕ) :
    fockDerivativeCoefficient ξ m =
      ξ (m + 1) * (fockDenominator (m + 1) : ℂ) / (m.factorial : ℂ) := by
  have hden : (fockDenominator (m + 1) : ℂ) * fockDenominator (m + 1) =
      ((m + 1).factorial : ℕ) := by
    norm_cast
    exact Real.mul_self_sqrt (by positivity)
  have hfac : (m.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [fockDerivativeCoefficient, fockCoefficient]
  field_simp [fockDenominator_ne_zero, hfac]
  rw [pow_two, hden, Nat.factorial_succ]
  push_cast
  ring

private theorem fock_derivSeries_eq (ξ : ℕ → ℂ) :
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (fockPowerSeries ξ).derivSeries =
      FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ) := by
  apply funext
  intro m
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (fockPowerSeries ξ).derivSeries) m,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq
      (FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ)) m]
  congr 1
  rw [FormalMultilinearSeries.coeff_ofScalars]
  change ((fockPowerSeries ξ).derivSeries.coeff m) 1 = fockDerivativeCoefficient ξ m
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simp [fockPowerSeries, fockDerivativeCoefficient, nsmul_eq_mul]

/-- The derivative has its coefficientwise differentiated power series on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_deriv_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    HasFPowerSeriesOnBall (deriv (fockFunction ξ))
      (FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ)) 0 ⊤ := by
  have h := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall
    (hasFPowerSeriesOnBall_fockFunction ξ hξ).fderiv
  rw [fock_derivSeries_eq ξ] at h
  apply h.congr
  intro z _
  exact fderiv_apply_one_eq_deriv

/-- The first derivative of a Fock series, in coefficientwise differentiated form. -/
theorem deriv_fockFunction_eq_tsum (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    deriv (fockFunction ξ) z =
      ∑' m : ℕ, (m + 1) * fockCoefficient ξ (m + 1) * z ^ m := by
  have h := hasFPowerSeriesOnBall_deriv_fockFunction ξ hξ
  calc
    deriv (fockFunction ξ) z =
        (FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ)).sum z := by
      simpa using h.sum (by simp)
    _ = ∑' m : ℕ, (m + 1) * fockCoefficient ξ (m + 1) * z ^ m := by
      rw [FormalMultilinearSeries.sum]
      apply tsum_congr
      intro m
      rw [FormalMultilinearSeries.ofScalars_apply_eq]
      simp [fockDerivativeCoefficient]

/-- The first derivative in the Fock factorial normalization. -/
theorem deriv_fockFunction_eq_tsum_factorial (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    deriv (fockFunction ξ) z =
      ∑' m : ℕ, ξ (m + 1) * Real.sqrt ((m + 1).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
  rw [deriv_fockFunction_eq_tsum ξ hξ z]
  apply tsum_congr
  intro m
  rw [← fockDerivativeCoefficient, fockDerivativeCoefficient_eq_factorial]
  rfl

private theorem hasFiniteFPowerSeriesOnBall_polynomial (p : ℂ[X]) :
    HasFiniteFPowerSeriesOnBall (fun z : ℂ => p.eval z)
      (FormalMultilinearSeries.ofScalars ℂ p.coeff) 0 (p.natDegree + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro m hm
    apply FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero
    exact p.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hm)
  · exact ENNReal.zero_lt_top
  · intro z _
    simp [Polynomial.eval_eq_sum_range, mul_comm]

private theorem fockCoefficient_ne_zero {ξ : ℕ → ℂ} {k : ℕ} (hξ : ξ k ≠ 0) :
    fockCoefficient ξ k ≠ 0 := by
  apply div_ne_zero hξ
  exact Complex.ofReal_ne_zero.mpr (fockDenominator_ne_zero k)

/-- If every input coefficient is nonzero, the Fock function is not the evaluation of `p`. -/
theorem fockFunction_ne_polynomial_eval (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (hξ0 : ∀ k, ξ k ≠ 0) (p : ℂ[X]) :
    fockFunction ξ ≠ fun z : ℂ => p.eval z := by
  intro h
  have hp : HasFPowerSeriesAt (fockFunction ξ)
      (FormalMultilinearSeries.ofScalars ℂ p.coeff) 0 := by
    rw [h]
    exact (hasFiniteFPowerSeriesOnBall_polynomial p).hasFiniteFPowerSeriesAt.hasFPowerSeriesAt
  have heq : fockPowerSeries ξ = FormalMultilinearSeries.ofScalars ℂ p.coeff :=
    (hasFPowerSeriesOnBall_fockFunction ξ hξ).hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  let n := p.natDegree + 1
  have hcoeff : fockCoefficient ξ n = p.coeff n := by
    simpa [fockPowerSeries] using
      congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff n) heq
  have hpzero : p.coeff n = 0 :=
    p.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  exact fockCoefficient_ne_zero (hξ0 n) (hcoeff.trans hpzero)

/-- If every input coefficient is nonzero, no complex polynomial represents the Fock function. -/
theorem not_exists_polynomial_eval_eq_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (hξ0 : ∀ k, ξ k ≠ 0) :
    ¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = fockFunction ξ z := by
  rintro ⟨p, hp⟩
  apply fockFunction_ne_polynomial_eval ξ hξ hξ0 p
  funext z
  exact (hp z).symm

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/FockDerivatives.lean. -/
section


/-!
# Iterated derivatives of the beta = 1/2 Fock series

This file gives the exact coefficient formula for every iterated derivative of a bounded-coefficient
Fock series. It also records summability, entire analyticity, and measurability in the coefficient
sequence.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace CofiniteDerivatives

noncomputable section

/-- The coefficient of degree `m` in the `n`-th derivative of a Fock series. -/
def fockIteratedCoefficient (ξ : ℕ → ℂ) (n m : ℕ) : ℂ :=
  ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) / (m.factorial : ℂ)

/-- The formal power series of the `n`-th derivative of a Fock series. -/
def fockIteratedPowerSeries (ξ : ℕ → ℂ) (n : ℕ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fockIteratedCoefficient ξ n)

private theorem fockIteratedCoefficient_zero (ξ : ℕ → ℂ) (m : ℕ) :
    fockIteratedCoefficient ξ 0 m = fockCoefficient ξ m := by
  have hden : (Real.sqrt (m.factorial : ℝ) : ℂ) * Real.sqrt (m.factorial : ℝ) =
      (m.factorial : ℕ) := by
    norm_cast
    exact Real.mul_self_sqrt (by positivity)
  have hfac : (m.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hsqrt : (Real.sqrt (m.factorial : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  rw [fockIteratedCoefficient, fockCoefficient, fockDenominator]
  simp only [zero_add]
  field_simp [hfac, hsqrt]
  rw [pow_two, hden]

private theorem fockIteratedCoefficient_succ (ξ : ℕ → ℂ) (n m : ℕ) :
    (m + 1) * fockIteratedCoefficient ξ n (m + 1) =
      fockIteratedCoefficient ξ (n + 1) m := by
  have hi : n + (m + 1) = n + 1 + m := by omega
  rw [fockIteratedCoefficient, fockIteratedCoefficient, hi, Nat.factorial_succ]
  push_cast
  field_simp

private theorem fockIteratedPowerSeries_zero (ξ : ℕ → ℂ) :
    fockIteratedPowerSeries ξ 0 = fockPowerSeries ξ := by
  ext m
  simp [fockIteratedPowerSeries, fockPowerSeries, fockIteratedCoefficient_zero]

private theorem fock_iterated_derivSeries_eq (ξ : ℕ → ℂ) (n : ℕ) :
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (fockIteratedPowerSeries ξ n).derivSeries =
      fockIteratedPowerSeries ξ (n + 1) := by
  change (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
      (FormalMultilinearSeries.ofScalars ℂ (fockIteratedCoefficient ξ n)).derivSeries =
    FormalMultilinearSeries.ofScalars ℂ (fockIteratedCoefficient ξ (n + 1))
  apply funext
  intro m
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (FormalMultilinearSeries.ofScalars ℂ
          (fockIteratedCoefficient ξ n)).derivSeries) m,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq
      (FormalMultilinearSeries.ofScalars ℂ
        (fockIteratedCoefficient ξ (n + 1))) m]
  congr 1
  rw [FormalMultilinearSeries.coeff_ofScalars]
  change ((FormalMultilinearSeries.ofScalars ℂ
    (fockIteratedCoefficient ξ n)).derivSeries.coeff m) 1 =
    fockIteratedCoefficient ξ (n + 1) m
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simpa [nsmul_eq_mul] using
    fockIteratedCoefficient_succ ξ n m

/-- The exact formal power series of every iterated derivative, valid on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_iteratedDeriv_fockFunction
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv n (fockFunction ξ))
      (fockIteratedPowerSeries ξ n) 0 ⊤ := by
  induction n with
  | zero =>
      rw [iteratedDeriv_zero, fockIteratedPowerSeries_zero]
      exact hasFPowerSeriesOnBall_fockFunction ξ hξ
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have h := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall ih.fderiv
      rw [fock_iterated_derivSeries_eq ξ n] at h
      apply h.congr
      intro z _
      exact fderiv_apply_one_eq_deriv

/-- The exact all-orders derivative formula in the Fock factorial normalization. -/
theorem iteratedDeriv_fockFunction_eq_tsum
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fockFunction ξ) z =
      ∑' m : ℕ, ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
  have h := hasFPowerSeriesOnBall_iteratedDeriv_fockFunction ξ hξ n
  calc
    iteratedDeriv n (fockFunction ξ) z = (fockIteratedPowerSeries ξ n).sum z := by
      simpa using h.sum (by simp)
    _ = ∑' m : ℕ, ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
      rw [FormalMultilinearSeries.sum]
      apply tsum_congr
      intro m
      simp [fockIteratedPowerSeries, fockIteratedCoefficient, mul_comm]

/-- The series in the exact all-orders derivative formula is summable at every point. -/
theorem summable_fockIteratedSeries
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    Summable fun m : ℕ => ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
      (m.factorial : ℂ) * z ^ m := by
  have h := (hasFPowerSeriesOnBall_iteratedDeriv_fockFunction ξ hξ n).hasSum
    (show z ∈ Metric.eball (0 : ℂ) (⊤ : ℝ≥0∞) by simp)
  simpa [fockIteratedPowerSeries, fockIteratedCoefficient,
    FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h.summable

/-- Every iterated derivative of a bounded-coefficient Fock series is entire. -/
theorem analyticOnNhd_iteratedDeriv_fockFunction
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n (fockFunction ξ)) Set.univ := by
  intro z _
  exact (hasFPowerSeriesOnBall_iteratedDeriv_fockFunction ξ hξ n).analyticAt_of_mem (by simp)

/-- Coefficient sequences in the closed unit disk, with the measurable structure inherited from
the full product space `ℕ → ℂ`. -/
abbrev BoundedFockCoefficients := {ξ : ℕ → ℂ // ∀ k, ‖ξ k‖ ≤ 1}

/-- Evaluation of an iterated Fock derivative is measurable in a bounded coefficient sequence. -/
theorem measurable_iteratedDeriv_fockFunction (n : ℕ) (z : ℂ) :
    Measurable (fun ξ : BoundedFockCoefficients =>
      iteratedDeriv n (fockFunction ξ.1) z) := by
  let partialSum : ℕ → BoundedFockCoefficients → ℂ := fun N ξ =>
    ∑ m ∈ Finset.range N,
      ξ.1 (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m
  have hpartial : ∀ N, Measurable (partialSum N) := by
    intro N
    dsimp [partialSum]
    refine Finset.measurable_fun_sum (Finset.range N) fun m _ => ?_
    have hcoord : Measurable (fun ξ : BoundedFockCoefficients => ξ.1 (n + m)) :=
      (measurable_pi_apply (X := fun _ : ℕ => ℂ) (n + m)).comp measurable_subtype_coe
    simpa only [div_eq_mul_inv, mul_assoc] using
      hcoord.mul_const ((Real.sqrt ((n + m).factorial : ℝ) : ℂ) /
        (m.factorial : ℂ) * z ^ m)
  apply measurable_of_tendsto_metrizable hpartial
  rw [tendsto_pi_nhds]
  intro ξ
  rw [iteratedDeriv_fockFunction_eq_tsum ξ.1 ξ.2 n z]
  exact (summable_fockIteratedSeries ξ.1 ξ.2 n z).hasSum.tendsto_sum_nat

/-- Evaluation of an iterated Fock derivative is almost everywhere measurable for every measure
on the bounded coefficient space. -/
theorem aemeasurable_iteratedDeriv_fockFunction_bounded
    (n : ℕ) (z : ℂ) (μ : Measure BoundedFockCoefficients) :
    AEMeasurable (fun ξ : BoundedFockCoefficients =>
      iteratedDeriv n (fockFunction ξ.1) z) μ :=
  (measurable_iteratedDeriv_fockFunction n z).aemeasurable

/-- Under any measure supported on bounded coefficient sequences, evaluation of the `n`-th Fock
derivative at `z` is almost everywhere measurable in the coefficient sequence. -/
theorem aemeasurable_iteratedDeriv_fockFunction
    (n : ℕ) (z : ℂ) (μ : Measure (ℕ → ℂ))
    (hμ : ∀ᵐ ξ ∂μ, ∀ k, ‖ξ k‖ ≤ 1) :
    AEMeasurable (fun ξ : ℕ → ℂ => iteratedDeriv n (fockFunction ξ) z) μ := by
  let partialSum : ℕ → (ℕ → ℂ) → ℂ := fun N ξ =>
    ∑ m ∈ Finset.range N,
      ξ (n + m) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m
  have hpartial : ∀ N, Measurable (partialSum N) := by
    intro N
    dsimp [partialSum]
    measurability
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun N => (hpartial N).aemeasurable)
  filter_upwards [hμ] with ξ hξ
  rw [iteratedDeriv_fockFunction_eq_tsum ξ hξ n z]
  exact (summable_fockIteratedSeries ξ hξ n z).hasSum.tendsto_sum_nat

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/InfinitePiSplit.lean. -/
section

open MeasureTheory ProbabilityTheory

namespace CofiniteDerivatives

section Split

variable {ι : Type*} [DecidableEq ι]
variable (X : ι → Type*) [∀ i, MeasurableSpace (X i)]

/-- Split a dependent product into one chosen coordinate and all remaining coordinates. -/
def piSplitAt (j : ι) :
    (∀ i, X i) ≃ᵐ X j × (∀ i : {i // i ≠ j}, X i) where
  toEquiv := Equiv.piSplitAt j X
  measurable_toFun :=
    (measurable_pi_apply j).prodMk <| measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun i ↦ by
    by_cases hi : i = j
    · subst i
      simpa [Equiv.piSplitAt] using
        (measurable_fst : Measurable (Prod.fst : X j × (∀ i : {i // i ≠ j}, X i) → X j))
    · convert (measurable_pi_apply ⟨i, hi⟩).comp
          (measurable_snd : Measurable (Prod.snd :
            X j × (∀ i : {i // i ≠ j}, X i) → (∀ i : {i // i ≠ j}, X i))) using 1
      funext x
      simp [Equiv.piSplitAt, hi]

@[simp]
theorem piSplitAt_apply_fst (j : ι) (x : ∀ i, X i) :
    (piSplitAt X j x).1 = x j := rfl

@[simp]
theorem piSplitAt_apply_snd (j : ι) (x : ∀ i, X i) (i : {i // i ≠ j}) :
    (piSplitAt X j x).2 i = x i := rfl

end Split

section MeasureSplit

variable {ι : Type*}
variable (X : ι → Type*) [∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Under an infinite product measure, one coordinate is independent of the tuple of all the
remaining coordinates. -/
theorem indepFun_eval_restrict (j : ι) :
    IndepFun (fun x : ∀ i, X i ↦ x j)
      (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i)
      (Measure.infinitePi μ) := by
  rw [IndepFun_iff_Indep]
  let m : ι → MeasurableSpace (∀ i, X i) := fun i ↦
    (inferInstance : MeasurableSpace (X i)).comap (fun x : ∀ i, X i ↦ x i)
  have h_indep :
      iIndep m (Measure.infinitePi μ) :=
    (iIndepFun_infinitePi (P := μ) (X := fun _ ↦ id) (fun _ ↦ measurable_id)).iIndep
  have h := indep_iSup_of_disjoint
    (m := m) (μ := Measure.infinitePi μ)
    (fun i ↦ (measurable_pi_apply i).comap_le) h_indep
    (S := ({j} : Set ι)) (T := {i | i ≠ j}) (by simp)
  have h_left : (⨆ i ∈ ({j} : Set ι), m i) = m j := by simp
  have h_right :
      (⨆ i ∈ {i | i ≠ j}, m i) =
        MeasurableSpace.comap
          (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i) inferInstance := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp, Function.comp_def, Set.mem_setOf_eq]
    exact iSup_subtype'
  rw [h_left, h_right] at h
  exact h

variable [DecidableEq ι]

/-- The coordinate split sends an infinite product measure to the binary product of the chosen
coordinate law and the infinite product of all remaining coordinate laws. -/
theorem infinitePi_map_piSplitAt (j : ι) :
    (Measure.infinitePi μ).map (piSplitAt X j) =
      (μ j).prod (Measure.infinitePi fun i : {i // i ≠ j} ↦ μ i) := by
  have h_eval : AEMeasurable (fun x : ∀ i, X i ↦ x j) (Measure.infinitePi μ) :=
    (measurable_pi_apply j).aemeasurable
  have h_restrict_meas : Measurable
      (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i) := by
    rw [measurable_pi_iff]
    exact fun i ↦ measurable_pi_apply (X := X) i.1
  have h_restrict : AEMeasurable
      (fun x : (∀ i, X i) ↦ fun i : {i // i ≠ j} ↦ x i) (Measure.infinitePi μ) :=
    h_restrict_meas.aemeasurable
  change (Measure.infinitePi μ).map
    (fun x : ∀ i, X i ↦ (x j, fun i : {i // i ≠ j} ↦ x i)) = _
  rw [(indepFun_iff_map_prod_eq_prod_map_map h_eval h_restrict).1
    (indepFun_eval_restrict X μ j), Measure.infinitePi_map_eval]
  congr 1
  exact Measure.infinitePi_map_restrict' μ

/-- The measurable coordinate split is measure preserving for infinite product measures. -/
theorem measurePreserving_piSplitAt (j : ι) :
    MeasurePreserving (piSplitAt X j) (Measure.infinitePi μ)
      ((μ j).prod (Measure.infinitePi fun i : {i // i ≠ j} ↦ μ i)) where
  measurable := (piSplitAt X j).measurable
  map_eq := infinitePi_map_piSplitAt X μ j

end MeasureSplit

section SmallBall

variable {ι : Type*} [DecidableEq ι]
variable (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]

/-- Fubini small-ball bound for an affine function of one coordinate. The remainder `H` is
defined on the complementary product, so its independence from coordinate `j` is encoded in its
type. -/
theorem infinitePi_affine_smallBall (j : ι) (a : ℂ)
  (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
  (ε : ℝ) (C : ENNReal)
    (hsmall : ∀ w : ℂ, μ j {z | ‖a * z + w‖ < ε} ≤ C) :
    Measure.infinitePi μ
    {ω : ι → ℂ | ‖a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)‖ < ε} ≤ C := by
  let S : Set (ℂ × (∀ i : {i // i ≠ j}, ℂ)) :=
    {p | ‖a * p.1 + H p.2‖ < ε}
  have hS : MeasurableSet S := by
    exact measurableSet_lt
      ((measurable_const.mul measurable_fst).add (hH.comp measurable_snd)).norm
      measurable_const
  have hpre :
      {ω : ι → ℂ | ‖a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)‖ < ε} =
        piSplitAt (fun _ : ι ↦ ℂ) j ⁻¹' S := rfl
  rw [hpre, ← Measure.map_apply (piSplitAt (fun _ : ι ↦ ℂ) j).measurable hS,
    infinitePi_map_piSplitAt (fun _ : ι ↦ ℂ) μ j, Measure.prod_apply_symm hS]
  apply lintegral_le_const
  exact ae_of_all _ fun y ↦ by simpa [S] using hsmall (H y)

/-- Full-product form of `infinitePi_affine_smallBall`. The equality hypothesis says precisely
that `H` depends only on coordinates other than `j`. -/
theorem infinitePi_affine_smallBall_of_factor (j : ι) (a : ℂ)
  (H : (ι → ℂ) → ℂ) (H₀ : ({i // i ≠ j} → ℂ) → ℂ)
    (hH₀ : Measurable H₀)
    (hH : ∀ ω, H ω = H₀ (fun i : {i // i ≠ j} ↦ ω i))
    (ε : ℝ) (C : ENNReal)
    (hsmall : ∀ w : ℂ, μ j {z | ‖a * z + w‖ < ε} ≤ C) :
    Measure.infinitePi μ {ω : ι → ℂ | ‖a * ω j + H ω‖ < ε} ≤ C := by
  simpa only [hH] using infinitePi_affine_smallBall μ j a H₀ hH₀ ε C hsmall

/-- Version with the selected coordinate law named separately as `ν`. -/
theorem infinitePi_affine_smallBall_of_law (j : ι) (ν : Measure ℂ) (hν : μ j = ν)
    (a : ℂ) (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (ε : ℝ) (C : ENNReal)
    (hsmall : ∀ w : ℂ, ν {z | ‖a * z + w‖ < ε} ≤ C) :
    Measure.infinitePi μ
        {ω : ι → ℂ | ‖a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)‖ < ε} ≤ C := by
  apply infinitePi_affine_smallBall μ j a H hH ε C
  intro w
  simpa only [hν] using hsmall w

end SmallBall

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/PointwiseLogTail.lean. -/
section

open MeasureTheory Real Set
open scoped ENNReal

namespace CofiniteDerivatives

noncomputable section

/-- The deterministic pointwise potential
`P_n(z) = log (sqrt (n!)) + |z| sqrt n`. -/
def pointwisePotential (n : ℕ) (z : ℂ) : ℝ :=
  Real.log (Real.sqrt (Nat.factorial n : ℝ)) + ‖z‖ * Real.sqrt n

/-- The `m`-th complex saddle monomial in the `n`-th derivative tail. -/
def saddleMonomial (n m : ℕ) (z : ℂ) : ℂ :=
  (Real.sqrt (Nat.factorial (n + m) : ℝ) / (Nat.factorial m : ℝ) : ℝ) * z ^ m

@[simp]
theorem norm_saddleMonomial (n m : ℕ) (z : ℂ) :
    ‖saddleMonomial n m z‖ = saddleCoeff n m ‖z‖ := by
  simp only [saddleMonomial, saddleCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow]
  rw [abs_of_nonneg]
  positivity

/-- The factorially weighted tail representing the `n`-th derivative after shifting the
coefficient sequence by `n`. -/
def pointwiseDerivativeSeries (ξ : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, ξ (n + m) * saddleMonomial n m z

/-- The pointwise saddle series is exactly the `n`-th derivative of the Fock function. -/
theorem pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    pointwiseDerivativeSeries ξ n z = iteratedDeriv n (fockFunction ξ) z := by
  rw [pointwiseDerivativeSeries, iteratedDeriv_fockFunction_eq_tsum ξ hξ n z]
  apply tsum_congr
  intro m
  simp only [saddleMonomial]
  push_cast
  ring

/-- The saddle coordinate nearest to `|z| sqrt n`. -/
def pointwiseSaddleIndex (n : ℕ) (z : ℂ) : ℕ :=
  ⌊‖z‖ * Real.sqrt n⌋₊

/-- The logarithmic loss in the floor saddle-coefficient estimate. -/
def pointwiseSaddleLoss (n : ℕ) : ℝ :=
  2 + Real.log n / 2

/-- Explicit conditions saying that `n` is large enough for every point in the annulus
`δ ≤ |z| ≤ R` to lie in the floor saddle range. -/
def PointwiseSaddleReady (n : ℕ) (δ R : ℝ) : Prop :=
  1 ≤ δ * Real.sqrt n ∧ R ≤ Real.sqrt n

theorem summable_saddleCoeff (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun m : ℕ ↦ saddleCoeff n m r) := by
  refine (normalizedSaddleSeries_summable n hr).mul_left
    (Real.sqrt (Nat.factorial n : ℝ)) |>.congr ?_
  intro m
  exact (saddleCoeff_eq_sqrt_factorial_mul_normalized n m r).symm

theorem summable_pointwiseDerivativeSeries {ξ : ℕ → ℂ} (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (n : ℕ) (z : ℂ) :
    Summable (fun m : ℕ ↦ ξ (n + m) * saddleMonomial n m z) := by
  apply Summable.of_norm
  exact (summable_saddleCoeff n (norm_nonneg z)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun m ↦ by
      rw [norm_mul, norm_saddleMonomial]
      exact mul_le_of_le_one_left (by
        rw [saddleCoeff]
        positivity) (hξ (n + m))

/-- Bounded coefficients make the derivative tail no larger than the deterministic saddle
series at the same radius. -/
theorem norm_pointwiseDerivativeSeries_le_saddleSeries {ξ : ℕ → ℂ}
    (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    ‖pointwiseDerivativeSeries ξ n z‖ ≤ saddleSeries n ‖z‖ := by
  calc
    ‖pointwiseDerivativeSeries ξ n z‖ ≤
        ∑' m : ℕ, ‖ξ (n + m) * saddleMonomial n m z‖ := by
      exact norm_tsum_le_tsum_norm
        ((summable_pointwiseDerivativeSeries hξ n z).norm)
    _ ≤ ∑' m : ℕ, saddleCoeff n m ‖z‖ := by
      exact (summable_pointwiseDerivativeSeries hξ n z).norm.tsum_le_tsum
        (fun m ↦ by
          rw [norm_mul, norm_saddleMonomial]
          exact mul_le_of_le_one_left (by
            rw [saddleCoeff]
            positivity) (hξ (n + m)))
        (summable_saddleCoeff n (norm_nonneg z))
    _ = saddleSeries n ‖z‖ := rfl

/-- Any function majorized by `saddleSeries` obeys the compact deterministic logarithmic
upper bound. This is the reusable deterministic half of the pointwise log estimate. -/
theorem log_norm_sub_pointwisePotential_le_of_norm_le_saddleSeries
    (F : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) (R : ℝ) (hn : n ≠ 0)
    (hzR : ‖z‖ ≤ R) (hF : ‖F n z‖ ≤ saddleSeries n ‖z‖) :
    Real.log ‖F n z‖ - pointwisePotential n z ≤ (R + R ^ 2) / 2 := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hzR
  by_cases hzero : F n z = 0
  · have hfactorial : (1 : ℝ) ≤ Real.sqrt (Nat.factorial n : ℝ) := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.factorial_ne_zero
    have hpotential : 0 ≤ pointwisePotential n z := by
      dsimp only [pointwisePotential]
      exact add_nonneg (Real.log_nonneg hfactorial)
        (mul_nonneg (norm_nonneg z) (Real.sqrt_nonneg _))
    simp only [hzero, norm_zero, Real.log_zero]
    nlinarith [sq_nonneg R]
  · have hlog : Real.log ‖F n z‖ ≤ Real.log (saddleSeries n ‖z‖) :=
      Real.log_le_log (norm_pos_iff.mpr hzero) hF
    have hsaddle := log_saddleSeries_le_on_compact n hn (norm_nonneg z) hzR
    dsimp only [pointwisePotential]
    rw [Real.log_sqrt (by positivity)]
    linarith

/-- Deterministic compact upper bound for the factorially weighted derivative tail. -/
theorem log_norm_pointwiseDerivativeSeries_sub_potential_le {ξ : ℕ → ℂ}
    (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) (R : ℝ) (hn : n ≠ 0)
    (hzR : ‖z‖ ≤ R) :
    Real.log ‖pointwiseDerivativeSeries ξ n z‖ - pointwisePotential n z ≤
      (R + R ^ 2) / 2 := by
  exact log_norm_sub_pointwisePotential_le_of_norm_le_saddleSeries
    (fun n z ↦ pointwiseDerivativeSeries ξ n z) n z R hn hzR
    (norm_pointwiseDerivativeSeries_le_saddleSeries hξ n z)

/-- Deterministic compact upper bound for the actual `n`-th Fock derivative. -/
theorem log_norm_iteratedDeriv_fockFunction_sub_potential_le
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (n : ℕ) (z : ℂ) (R : ℝ) (hn : n ≠ 0) (hzR : ‖z‖ ≤ R) :
    Real.log ‖iteratedDeriv n (fockFunction ξ) z‖ - pointwisePotential n z ≤
      (R + R ^ 2) / 2 := by
  rw [← pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction ξ hξ n z]
  exact log_norm_pointwiseDerivativeSeries_sub_potential_le hξ n z R hn hzR

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `F` has the quadratic small-ball bound supplied by an affine coordinate with coefficient
`a`. This is the interface expected from conditioning on all other random coordinates. -/
def HasQuadraticSmallBall (μ : Measure Ω) (F : Ω → ℂ) (a : ℂ) : Prop :=
  ∀ ε : ℝ, 0 ≤ ε →
    μ {ω | ‖F ω‖ < ε} ≤ ENNReal.ofReal ((ε / ‖a‖) ^ 2)

/-- An affine function of one uniform-disk coordinate has the required quadratic small-ball
bound. -/
theorem uniformDisk_affine_hasQuadraticSmallBall {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    HasQuadraticSmallBall uniformDisk (fun u ↦ a * u + w) a := by
  intro ε hε
  exact uniformDisk_affine_smallBall ha w hε

/-- Splitting an infinite product at a uniform-disk coordinate promotes the one-coordinate
affine estimate to a quadratic small-ball bound for the full random sum. -/
theorem infinitePi_uniformDisk_affine_hasQuadraticSmallBall
    {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk) {a : ℂ} (ha : a ≠ 0)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H) :
    HasQuadraticSmallBall (Measure.infinitePi μ)
      (fun ω ↦ a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)) a := by
  intro ε hε
  apply infinitePi_affine_smallBall_of_law μ j uniformDisk hμj a H hH ε
    (ENNReal.ofReal ((ε / ‖a‖) ^ 2))
  intro w
  exact uniformDisk_affine_smallBall ha w hε

/-- A quadratic small-ball estimate at a coefficient whose logarithm reaches the potential up
to `loss` gives an `exp (-2s)` lower tail for the logarithm. The hypothesis is deliberately
abstract so a later infinite-product split can discharge it by conditioning. -/
theorem measure_pointwisePotential_sub_log_norm_gt_le_exp_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ) (a : ℂ)
    (n : ℕ) (z : ℂ) (loss s : ℝ) (ha : a ≠ 0)
    (hscale : pointwisePotential n z - loss ≤ Real.log ‖a‖)
    (hsmall : HasQuadraticSmallBall μ F a) :
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ > s + loss} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  let ε : ℝ := Real.exp (pointwisePotential n z - (s + loss))
  have hε : 0 ≤ ε := Real.exp_nonneg _
  have hsubset :
      {ω | pointwisePotential n z - Real.log ‖F ω‖ > s + loss} ⊆
        {ω | ‖F ω‖ < ε} := by
    intro ω hω
    change pointwisePotential n z - Real.log ‖F ω‖ > s + loss at hω
    change ‖F ω‖ < Real.exp (pointwisePotential n z - (s + loss))
    by_cases hzero : F ω = 0
    · simpa [hzero] using Real.exp_pos (pointwisePotential n z - (s + loss))
    · rw [← Real.exp_log (norm_pos_iff.mpr hzero)]
      apply Real.exp_lt_exp.mpr
      linarith
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hscale_exp :
      Real.exp (pointwisePotential n z - loss) ≤ ‖a‖ := by
    calc
      Real.exp (pointwisePotential n z - loss) ≤ Real.exp (Real.log ‖a‖) :=
        Real.exp_le_exp.mpr hscale
      _ = ‖a‖ := Real.exp_log ha_norm
  have hratio : ε / ‖a‖ ≤ Real.exp (-s) := by
    rw [div_le_iff₀ ha_norm]
    calc
      ε = Real.exp (-s) * Real.exp (pointwisePotential n z - loss) := by
        dsimp only [ε]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-s) * ‖a‖ := by
        exact mul_le_mul_of_nonneg_left hscale_exp (Real.exp_nonneg _)
  have hratio_nonneg : 0 ≤ ε / ‖a‖ := div_nonneg hε ha_norm.le
  have hsquare : (ε / ‖a‖) ^ 2 ≤ (Real.exp (-s)) ^ 2 := by
    nlinarith [Real.exp_nonneg (-s)]
  calc
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ > s + loss} ≤
        μ {ω | ‖F ω‖ < ε} := measure_mono hsubset
    _ ≤ ENNReal.ofReal ((ε / ‖a‖) ^ 2) := hsmall ε hε
    _ ≤ ENNReal.ofReal ((Real.exp (-s)) ^ 2) := ENNReal.ofReal_le_ofReal hsquare
    _ = ENNReal.ofReal (Real.exp (-2 * s)) := by
      congr 2
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- The floor saddle monomial reaches the deterministic potential up to
`2 + log n / 2` whenever `n` is in the eventual saddle range for `z`. -/
theorem pointwisePotential_sub_saddleLoss_le_log_norm_saddleMonomial
    (n : ℕ) (z : ℂ) (hx : 1 ≤ ‖z‖ * Real.sqrt n)
    (hzn : ‖z‖ ≤ Real.sqrt n) :
    pointwisePotential n z - pointwiseSaddleLoss n ≤
      Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z‖ := by
  have hcoeff := log_saddleCoeff_floor_lower n (norm_nonneg z) hx hzn
  rw [norm_saddleMonomial]
  dsimp only [pointwisePotential, pointwiseSaddleLoss, pointwiseSaddleIndex]
  rw [Real.log_sqrt (by positivity)]
  linarith

theorem saddleMonomial_pointwiseSaddleIndex_ne_zero
    (n : ℕ) (z : ℂ) (hx : 1 ≤ ‖z‖ * Real.sqrt n) :
    saddleMonomial n (pointwiseSaddleIndex n z) z ≠ 0 := by
  have hz : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hx
  rw [saddleMonomial]
  exact mul_ne_zero (by
    norm_cast
    exact div_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)) (by positivity))
    (pow_ne_zero _ hz)

/-- Abstract conditional lower tail at the floor saddle coordinate. A product-coordinate split
only needs to prove `hsmall`, normally by `uniformDisk_affine_smallBall` after fixing the other
coordinates. -/
theorem measure_pointwise_floor_lowerTail_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ)
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n)
    (hsmall : HasQuadraticSmallBall μ F
      (saddleMonomial n (pointwiseSaddleIndex n z) z)) :
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  exact measure_pointwisePotential_sub_log_norm_gt_le_exp_of_smallBall
    μ F (saddleMonomial n (pointwiseSaddleIndex n z) z) n z
    (pointwiseSaddleLoss n) s
    (saddleMonomial_pointwiseSaddleIndex_ne_zero n z hx)
    (pointwisePotential_sub_saddleLoss_le_log_norm_saddleMonomial n z hx hzn)
    hsmall

/-- Concrete one-coordinate version of the floor lower tail for a uniform-disk coordinate and
an arbitrary fixed remainder. -/
theorem uniformDisk_pointwise_floor_lowerTail
    (n : ℕ) (z w : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    uniformDisk {u | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * u + w‖ >
          s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_floor_lowerTail_of_smallBall uniformDisk
    (fun u ↦ saddleMonomial n (pointwiseSaddleIndex n z) z * u + w)
    n z s hx hzn
  exact uniformDisk_affine_hasQuadraticSmallBall
    (saddleMonomial_pointwiseSaddleIndex_ne_zero n z hx) w

/-- Full infinite-product floor lower tail after splitting off one uniform-disk coordinate.
The measurable function `H` is the remainder of the random sum. -/
theorem infinitePi_pointwise_floor_lowerTail
    {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    Measure.infinitePi μ {ω | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
          H (fun i : {i // i ≠ j} ↦ ω i)‖ >
            s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_floor_lowerTail_of_smallBall (Measure.infinitePi μ)
    (fun ω ↦ saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
      H (fun i : {i // i ≠ j} ↦ ω i)) n z s hx hzn
  exact infinitePi_uniformDisk_affine_hasQuadraticSmallBall μ j hμj
    (saddleMonomial_pointwiseSaddleIndex_ne_zero n z hx) H hH

/-- Full-product floor lower tail for a random function supplied together with its affine
saddle-coordinate decomposition. -/
theorem infinitePi_pointwise_floor_lowerTail_of_decomposition
    {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (F : (ι → ℂ) → ℂ) (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hF : ∀ ω, F ω = saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
      H (fun i : {i // i ≠ j} ↦ ω i))
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    Measure.infinitePi μ {ω | pointwisePotential n z - Real.log ‖F ω‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  simpa only [hF] using
    infinitePi_pointwise_floor_lowerTail μ j hμj H hH n z s hx hzn

/-- Abstract floor-coordinate lower tail, uniformly applicable once `n` is ready for the
annulus `δ ≤ |z| ≤ R`. -/
theorem measure_pointwise_annulus_lowerTail_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ)
    (n : ℕ) (z : ℂ) (δ R s : ℝ)
    (hn : PointwiseSaddleReady n δ R) (hzδ : δ ≤ ‖z‖) (hzR : ‖z‖ ≤ R)
    (hsmall : HasQuadraticSmallBall μ F
      (saddleMonomial n (pointwiseSaddleIndex n z) z)) :
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_floor_lowerTail_of_smallBall μ F n z s
  · exact hn.1.trans <| mul_le_mul_of_nonneg_right hzδ (Real.sqrt_nonneg _)
  · exact hzR.trans hn.2
  · exact hsmall

/-- Concrete conditional slice bound for every point in a saddle-ready annulus. -/
theorem uniformDisk_pointwise_annulus_lowerTail
    (n : ℕ) (z w : ℂ) (δ R s : ℝ)
    (hn : PointwiseSaddleReady n δ R) (hzδ : δ ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    uniformDisk {u | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * u + w‖ >
          s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  have hx : 1 ≤ ‖z‖ * Real.sqrt n :=
    hn.1.trans <| mul_le_mul_of_nonneg_right hzδ (Real.sqrt_nonneg _)
  exact uniformDisk_pointwise_floor_lowerTail n z w s hx (hzR.trans hn.2)

/-- Full infinite-product lower tail, uniformly applicable on a saddle-ready annulus. -/
theorem infinitePi_pointwise_annulus_lowerTail
    {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (z : ℂ) (δ R s : ℝ)
    (hn : PointwiseSaddleReady n δ R) (hzδ : δ ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    Measure.infinitePi μ {ω | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
          H (fun i : {i // i ≠ j} ↦ ω i)‖ >
            s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  have hx : 1 ≤ ‖z‖ * Real.sqrt n :=
    hn.1.trans <| mul_le_mul_of_nonneg_right hzδ (Real.sqrt_nonneg _)
  exact infinitePi_pointwise_floor_lowerTail μ j hμj H hH n z s hx (hzR.trans hn.2)

@[simp]
theorem saddleMonomial_zero_zero (n : ℕ) :
    saddleMonomial n 0 0 = (Real.sqrt (Nat.factorial n : ℝ) : ℂ) := by
  simp [saddleMonomial]

theorem saddleMonomial_zero_zero_ne_zero (n : ℕ) : saddleMonomial n 0 0 ≠ 0 := by
  rw [saddleMonomial_zero_zero]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))

/-- At `z = 0`, coordinate `m = 0` reaches the potential exactly, so there is no logarithmic
loss. -/
theorem pointwisePotential_zero_eq_log_norm_saddleMonomial_zero (n : ℕ) :
    pointwisePotential n 0 = Real.log ‖saddleMonomial n 0 0‖ := by
  rw [saddleMonomial_zero_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  simp [pointwisePotential]

/-- Abstract lower tail at the origin, using the zeroth coordinate. -/
theorem measure_pointwise_zero_lowerTail_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ)
    (n : ℕ) (s : ℝ)
    (hsmall : HasQuadraticSmallBall μ F (saddleMonomial n 0 0)) :
    μ {ω | pointwisePotential n 0 - Real.log ‖F ω‖ > s} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  simpa only [add_zero] using
    measure_pointwisePotential_sub_log_norm_gt_le_exp_of_smallBall
      μ F (saddleMonomial n 0 0) n 0 0 s (saddleMonomial_zero_zero_ne_zero n)
      (by rw [sub_zero, pointwisePotential_zero_eq_log_norm_saddleMonomial_zero]) hsmall

/-- Concrete uniform-disk lower tail at `z = 0`, with the coordinate `m = 0`. -/
theorem uniformDisk_pointwise_zero_lowerTail (n : ℕ) (w : ℂ) (s : ℝ) :
    uniformDisk {u | pointwisePotential n 0 -
        Real.log ‖saddleMonomial n 0 0 * u + w‖ > s} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_zero_lowerTail_of_smallBall uniformDisk
    (fun u ↦ saddleMonomial n 0 0 * u + w) n s
  exact uniformDisk_affine_hasQuadraticSmallBall (saddleMonomial_zero_zero_ne_zero n) w

/-- Full infinite-product lower tail at the origin, using coordinate `m = 0`. -/
theorem infinitePi_pointwise_zero_lowerTail
    {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (s : ℝ) :
    Measure.infinitePi μ {ω | pointwisePotential n 0 -
        Real.log ‖saddleMonomial n 0 0 * ω j +
          H (fun i : {i // i ≠ j} ↦ ω i)‖ > s} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_zero_lowerTail_of_smallBall (Measure.infinitePi μ)
    (fun ω ↦ saddleMonomial n 0 0 * ω j +
      H (fun i : {i // i ≠ j} ↦ ω i)) n s
  exact infinitePi_uniformDisk_affine_hasQuadraticSmallBall μ j hμj
    (saddleMonomial_zero_zero_ne_zero n) H hH

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/RandomFock.lean. -/
section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Polynomial Topology

namespace CofiniteDerivatives

noncomputable section

/-- The iid product law of uniform complex coefficients on the closed unit disk. -/
def P : Measure (ℕ → ℂ) :=
  Measure.infinitePi (fun _ : ℕ ↦ uniformDisk)

instance P.isProbabilityMeasure : IsProbabilityMeasure P := by
  unfold P
  infer_instance

/-- Keep points in the closed unit disk and send all other points to zero. -/
noncomputable def clipDisk (z : ℂ) : ℂ := by
  classical
  exact if z ∈ closedBall (0 : ℂ) 1 then z else 0

@[simp]
theorem clipDisk_eq_self {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    clipDisk z = z := by
  simp [clipDisk, hz]

@[simp]
theorem clipDisk_eq_zero {z : ℂ} (hz : z ∉ closedBall (0 : ℂ) 1) :
    clipDisk z = 0 := by
  simp [clipDisk, hz]

theorem measurable_clipDisk : Measurable clipDisk := by
  exact measurable_id.piecewise measurableSet_closedBall measurable_const

theorem norm_clipDisk_le_one (z : ℂ) : ‖clipDisk z‖ ≤ 1 := by
  by_cases hz : z ∈ closedBall (0 : ℂ) 1
  · rw [clipDisk_eq_self hz]
    simpa [mem_closedBall, dist_eq_norm] using hz
  · rw [clipDisk_eq_zero hz]
    simp

/-- The clipped random Fock sample path. -/
def randomFock (ω : ℕ → ℂ) : ℂ → ℂ :=
  fockFunction (fun k ↦ clipDisk (ω k))

/-- The `n`-th derivative of a clipped random Fock sample path. -/
def randomFockDeriv (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv n (randomFock ω) z

/-- Every clipped sample path is entire. -/
theorem analyticOnNhd_randomFock (ω : ℕ → ℂ) :
    AnalyticOnNhd ℂ (randomFock ω) Set.univ := by
  exact analyticOnNhd_fockFunction (fun k ↦ clipDisk (ω k))
    (fun k ↦ norm_clipDisk_le_one (ω k))

/-- Every iterated derivative of every clipped sample path is entire. -/
theorem analyticOnNhd_randomFockDeriv (n : ℕ) (ω : ℕ → ℂ) :
    AnalyticOnNhd ℂ (randomFockDeriv n ω) Set.univ := by
  exact analyticOnNhd_iteratedDeriv_fockFunction (fun k ↦ clipDisk (ω k))
    (fun k ↦ norm_clipDisk_le_one (ω k)) n

/-- Each coordinate lies in the closed unit disk almost surely. -/
theorem P_ae_coordinate_mem_closedBall (k : ℕ) :
    ∀ᵐ ω ∂P, ω k ∈ closedBall (0 : ℂ) 1 := by
  simpa [P] using
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ uniformDisk) k).quasiMeasurePreserving.ae
      uniformDisk_ae_mem_closedBall

/-- Each coordinate is nonzero almost surely. -/
theorem P_ae_coordinate_ne_zero (k : ℕ) :
    ∀ᵐ ω ∂P, ω k ≠ 0 := by
  have hnonzero : ∀ᵐ z ∂uniformDisk, z ≠ 0 := by
    rw [ae_iff]
    simpa only [compl_ofPred, not_ne_iff, ofPred_eq_eq_singleton] using
      uniformDisk_singleton 0
  simpa [P] using
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ uniformDisk) k).quasiMeasurePreserving.ae
      hnonzero

/-- Almost surely every coordinate is unchanged by clipping and is nonzero. -/
theorem P_ae_forall_clipDisk_eq_and_ne_zero :
    ∀ᵐ ω ∂P, ∀ k, clipDisk (ω k) = ω k ∧ ω k ≠ 0 := by
  rw [ae_all_iff]
  intro k
  filter_upwards [P_ae_coordinate_mem_closedBall k, P_ae_coordinate_ne_zero k] with ω hmem hne
  exact ⟨clipDisk_eq_self hmem, hne⟩

/-- Almost surely the random Fock sample path is not represented by a complex polynomial. -/
theorem P_ae_randomFock_nonpolynomial :
    ∀ᵐ ω ∂P, ¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = randomFock ω z := by
  filter_upwards [P_ae_forall_clipDisk_eq_and_ne_zero] with ω hω
  apply not_exists_polynomial_eval_eq_fockFunction
    (fun k ↦ clipDisk (ω k)) (fun k ↦ norm_clipDisk_le_one (ω k))
  intro k
  rw [(hω k).1]
  exact (hω k).2

/-- Exact series formula for a random Fock derivative. -/
theorem randomFockDeriv_eq_tsum (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) :
    randomFockDeriv n ω z =
      ∑' m : ℕ, clipDisk (ω (n + m)) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
  exact iteratedDeriv_fockFunction_eq_tsum (fun k ↦ clipDisk (ω k))
    (fun k ↦ norm_clipDisk_le_one (ω k)) n z

/-- Random Fock derivative evaluation is jointly measurable in the coefficient sequence and
the complex evaluation point. -/
theorem measurable_randomFockDeriv (n : ℕ) :
    Measurable (fun p : (ℕ → ℂ) × ℂ ↦ randomFockDeriv n p.1 p.2) := by
  let partialSum : ℕ → ((ℕ → ℂ) × ℂ) → ℂ := fun N p ↦
    ∑ m ∈ Finset.range N,
      clipDisk (p.1 (n + m)) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * p.2 ^ m
  have hpartial : ∀ N, Measurable (partialSum N) := by
    intro N
    dsimp [partialSum]
    refine Finset.measurable_fun_sum (Finset.range N) fun m _ ↦ ?_
    have hcoord : Measurable (fun p : (ℕ → ℂ) × ℂ ↦ clipDisk (p.1 (n + m))) :=
      measurable_clipDisk.comp ((measurable_pi_apply (n + m)).comp measurable_fst)
    exact ((hcoord.mul_const (Real.sqrt ((n + m).factorial : ℝ) : ℂ)).div_const
      (m.factorial : ℂ)).mul (measurable_snd.pow_const m)
  apply measurable_of_tendsto_metrizable hpartial
  rw [tendsto_pi_nhds]
  intro p
  rw [randomFockDeriv_eq_tsum]
  exact (summable_fockIteratedSeries (fun k ↦ clipDisk (p.1 k))
    (fun k ↦ norm_clipDisk_le_one (p.1 k)) n p.2).hasSum.tendsto_sum_nat

/-- A bounded coefficient sequence reconstructed from every coordinate except `j`, with the
missing coordinate set to zero. -/
def clippedWithout (j : ℕ) (η : {k // k ≠ j} → ℂ) (k : ℕ) : ℂ :=
  if hk : k = j then 0 else clipDisk (η ⟨k, hk⟩)

@[simp]
theorem clippedWithout_self (j : ℕ) (η : {k // k ≠ j} → ℂ) :
    clippedWithout j η j = 0 := by
  simp [clippedWithout]

@[simp]
theorem clippedWithout_ne {j k : ℕ} (η : {k // k ≠ j} → ℂ) (hk : k ≠ j) :
    clippedWithout j η k = clipDisk (η ⟨k, hk⟩) := by
  simp [clippedWithout, hk]

theorem norm_clippedWithout_le_one (j : ℕ) (η : {k // k ≠ j} → ℂ) (k : ℕ) :
    ‖clippedWithout j η k‖ ≤ 1 := by
  by_cases hk : k = j
  · simp [clippedWithout, hk]
  · rw [clippedWithout_ne η hk]
    exact norm_clipDisk_le_one _

/-- `clippedWithout` packaged as a bounded Fock coefficient sequence. -/
def boundedClippedWithout (j : ℕ) (η : {k // k ≠ j} → ℂ) :
    BoundedFockCoefficients :=
  ⟨clippedWithout j η, norm_clippedWithout_le_one j η⟩

theorem measurable_boundedClippedWithout (j : ℕ) :
    Measurable (boundedClippedWithout j) := by
  refine (measurable_pi_iff.2 fun k ↦ ?_).subtype_mk
  by_cases hk : k = j
  · subst k
    simpa [boundedClippedWithout] using
      (measurable_const : Measurable (fun _ : ({k // k ≠ j} → ℂ) ↦ (0 : ℂ)))
  · have hcoordinate : Measurable
        (fun η : ({q // q ≠ j} → ℂ) ↦ clipDisk (η ⟨k, hk⟩)) :=
      measurable_clipDisk.comp
        (measurable_pi_apply (X := fun _ : {q // q ≠ j} ↦ ℂ) ⟨k, hk⟩)
    simpa [boundedClippedWithout, clippedWithout, hk] using hcoordinate

/-- The derivative remainder after deleting the floor saddle coordinate. -/
def randomFockRemainder (n : ℕ) (z : ℂ)
    (η : {k // k ≠ n + pointwiseSaddleIndex n z} → ℂ) : ℂ :=
  iteratedDeriv n
    (fockFunction (boundedClippedWithout (n + pointwiseSaddleIndex n z) η).1) z

theorem measurable_randomFockRemainder (n : ℕ) (z : ℂ) :
    Measurable (randomFockRemainder n z) := by
  exact (measurable_iteratedDeriv_fockFunction n z).comp
    (measurable_boundedClippedWithout (n + pointwiseSaddleIndex n z))

/-- Split a pointwise derivative series into one term and the series with that coefficient
deleted. -/
theorem pointwiseDerivativeSeries_split (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (n m : ℕ) (z : ℂ) :
    pointwiseDerivativeSeries ξ n z =
      saddleMonomial n m z * ξ (n + m) +
        pointwiseDerivativeSeries (fun k ↦ if k = n + m then 0 else ξ k) n z := by
  rw [pointwiseDerivativeSeries,
    (summable_pointwiseDerivativeSeries hξ n z).tsum_eq_add_tsum_ite m,
    pointwiseDerivativeSeries]
  congr 1
  · ring
  · apply tsum_congr
    intro q
    by_cases hq : q = m
    · subst q
      simp
    · have hnq : n + q ≠ n + m := by omega
      simp [hq, hnq]

/-- Exact decomposition of a random Fock derivative into its clipped floor saddle coordinate
and a measurable function of all complementary coordinates. -/
theorem randomFockDeriv_decomposition (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) :
    randomFockDeriv n ω z =
      saddleMonomial n (pointwiseSaddleIndex n z) z *
          clipDisk (ω (n + pointwiseSaddleIndex n z)) +
        randomFockRemainder n z
          (fun i : {k // k ≠ n + pointwiseSaddleIndex n z} ↦ ω i) := by
  let m := pointwiseSaddleIndex n z
  let ξ : ℕ → ℂ := fun k ↦ clipDisk (ω k)
  have hξ : ∀ k, ‖ξ k‖ ≤ 1 := fun k ↦ norm_clipDisk_le_one (ω k)
  rw [randomFockDeriv, randomFock,
    ← pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction ξ hξ n z,
    pointwiseDerivativeSeries_split ξ hξ n m z]
  congr 1
  rw [randomFockRemainder,
    ← pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction
      (boundedClippedWithout (n + m)
        (fun i : {k // k ≠ n + m} ↦ ω i)).1
      (boundedClippedWithout (n + m)
        (fun i : {k // k ≠ n + m} ↦ ω i)).2 n z]
  apply tsum_congr
  intro q
  by_cases hq : q = m
  · subst q
    simp [pointwiseDerivativeSeries, boundedClippedWithout]
  · have hnq : n + q ≠ n + m := by omega
    simp [pointwiseDerivativeSeries, boundedClippedWithout, clippedWithout, hnq, ξ]

/-- The affine field obtained by exposing the raw saddle coordinate and clipping every
complementary coordinate. -/
def randomFockAffineSaddle (n : ℕ) (z : ℂ) (ω : ℕ → ℂ) : ℂ :=
  saddleMonomial n (pointwiseSaddleIndex n z) z *
      ω (n + pointwiseSaddleIndex n z) +
    randomFockRemainder n z
      (fun i : {k // k ≠ n + pointwiseSaddleIndex n z} ↦ ω i)

theorem measurable_randomFockAffineSaddle (n : ℕ) (z : ℂ) :
    Measurable (randomFockAffineSaddle n z) := by
  exact (measurable_const.mul (measurable_pi_apply _)).add
    ((measurable_randomFockRemainder n z).comp <|
      measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.1)

/-- On the full-measure support of the product law, the exposed raw coordinate is also
unchanged by clipping. -/
theorem randomFockDeriv_eq_affineSaddle_ae (n : ℕ) (z : ℂ) :
    (fun ω ↦ randomFockDeriv n ω z) =ᵐ[P] randomFockAffineSaddle n z := by
  filter_upwards [P_ae_coordinate_mem_closedBall (n + pointwiseSaddleIndex n z)] with ω hω
  rw [randomFockDeriv_decomposition, clipDisk_eq_self hω]
  rfl

/-- Pointwise logarithmic lower tail for the iid uniform-disk random Fock function. The
hypotheses are exactly the floor saddle range at the fixed pair `(n,z)`. -/
theorem P_pointwise_log_lowerTail
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    P {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  have hraw :
      P {ω | pointwisePotential n z - Real.log ‖randomFockAffineSaddle n z ω‖ >
          s + pointwiseSaddleLoss n} ≤
        ENNReal.ofReal (Real.exp (-2 * s)) := by
    simpa [P, randomFockAffineSaddle] using
      infinitePi_pointwise_floor_lowerTail
        (fun _ : ℕ ↦ uniformDisk) (n + pointwiseSaddleIndex n z) rfl
        (randomFockRemainder n z) (measurable_randomFockRemainder n z)
        n z s hx hzn
  calc
    P {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} =
        P {ω | pointwisePotential n z - Real.log ‖randomFockAffineSaddle n z ω‖ >
          s + pointwiseSaddleLoss n} := by
      apply measure_congr
      filter_upwards [randomFockDeriv_eq_affineSaddle_ae n z] with ω hω
      change
        (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
          s + pointwiseSaddleLoss n) =
        (pointwisePotential n z - Real.log ‖randomFockAffineSaddle n z ω‖ >
          s + pointwiseSaddleLoss n)
      rw [hω]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * s)) := hraw

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/FinalExtraction.lean. -/
section

open Filter MeasureTheory Set
open scoped ENNReal Polynomial

namespace CofiniteDerivatives

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]

/-- Intersect an almost-everywhere property with countably many Borel--Cantelli conclusions and
extract one deterministic sample. -/
theorem exists_ae_property_forall_eventually_not_failure
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : ι → ℕ → Set Ω) (Q : Ω → Prop)
    (hQ : ∀ᵐ ω ∂μ, Q ω)
    (hsum : ∀ j, (∑' n, μ (failure j n)) < ∞) :
    ∃ ω, Q ω ∧ ∀ j, ∀ᶠ n in atTop, ω ∉ failure j n := by
  have hfailure : ∀ᵐ ω ∂μ, ∀ j, ∀ᶠ n in atTop, ω ∉ failure j n := by
    rw [ae_all_iff]
    intro j
    exact ae_eventually_notMem (ne_of_lt (hsum j))
  have hboth : ∀ᵐ ω ∂μ, Q ω ∧ ∀ j, ∀ᶠ n in atTop, ω ∉ failure j n := by
    filter_upwards [hQ, hfailure] with ω hQω hfailureω
    exact ⟨hQω, hfailureω⟩
  exact hboth.exists

/-- The zero set of the `n`-th derivative of a random Fock sample. -/
def randomFockZeroSet (ω : ℕ → ℂ) (n : ℕ) : Set ℂ :=
  {z | randomFockDeriv n ω z = 0}

/-- The event that the `n`-th random Fock derivative has no zero in the `j`-th basis disk. -/
def randomFockDiskHole (j n : ℕ) : Set (ℕ → ℂ) :=
  holeEvent randomFockZeroSet diskBasis j n

/-- The final deterministic random-Fock extraction, conditional only on summability of the
disk-hole probabilities. -/
theorem exists_randomFock_final_of_summable_holes
    (hsum : ∀ j, (∑' n, P (randomFockDiskHole j n)) < ∞) :
    ∃ ω,
      AnalyticOnNhd ℂ (randomFock ω) Set.univ ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = randomFock ω z) ∧
      DerivativesCofinitelyHit (randomFock ω) ∧
      EveryDerivativeSubsequenceDense (randomFock ω) := by
  classical
  obtain ⟨ω, hnonpolynomial, hholes⟩ :=
    exists_ae_property_forall_eventually_not_failure
      (μ := P) (failure := randomFockDiskHole)
      (Q := fun ω ↦ ¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = randomFock ω z)
      P_ae_randomFock_nonpolynomial hsum
  have hcofinite : CofinitelyHits (randomFockZeroSet ω) := by
    intro U hU hUne
    obtain ⟨j, hjU⟩ := exists_diskBasis_subset U hU hUne
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hholes j)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hhit : (randomFockZeroSet ω n ∩ diskBasis j).Nonempty := by
      have hnotHole := hN n hn
      simpa only [randomFockDiskHole, holeEvent, mem_setOf_eq, not_not] using hnotHole
    rcases hhit with ⟨z, hzZero, hzDisk⟩
    exact ⟨z, hzZero, hjU hzDisk⟩
  have hderivatives : DerivativesCofinitelyHit (randomFock ω) := by
    exact hcofinite
  have hsubsequences : EveryDerivativeSubsequenceDense (randomFock ω) :=
    (derivativesCofinitelyHit_iff_everyDerivativeSubsequenceDense (randomFock ω)).mp
      hderivatives
  exact ⟨ω, analyticOnNhd_randomFock ω, hnonpolynomial, hderivatives, hsubsequences⟩

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/FockGrowth.lean. -/
section

open Real

namespace CofiniteDerivatives

noncomputable section

/-- Every bounded-coefficient Fock series has an explicit quadratic exponential majorant. -/
theorem norm_fockFunction_le_sqrt_two_mul_exp_sq
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    ‖fockFunction ξ z‖ ≤ √2 * Real.exp (‖z‖ ^ 2) := by
  have hderiv := norm_pointwiseDerivativeSeries_le_saddleSeries hξ 0 z
  rw [pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction ξ hξ, iteratedDeriv_zero]
    at hderiv
  refine hderiv.trans ?_
  rw [saddleSeries_eq_sqrt_factorial_mul_normalized]
  simp only [Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, one_mul]
  have hbound :=
    (normalizedSaddleSeries_summable_and_le_cauchySchwarz 0 (norm_nonneg z)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)).2
  calc
    normalizedSaddleSeries 0 ‖z‖ ≤
        √((1 / (1 - (1 / 2 : ℝ))) ^ (0 + 1)) *
          √(Real.exp (‖z‖ ^ 2 / (1 / 2 : ℝ))) := hbound
    _ = √2 * Real.exp (‖z‖ ^ 2) := by
      rw [show (1 / (1 - (1 / 2 : ℝ))) ^ (0 + 1) = 2 by norm_num]
      rw [show ‖z‖ ^ 2 / (1 / 2 : ℝ) = 2 * ‖z‖ ^ 2 by ring]
      rw [show 2 * ‖z‖ ^ 2 = ‖z‖ ^ 2 + ‖z‖ ^ 2 by ring, Real.exp_add,
        Real.sqrt_mul_self (Real.exp_nonneg _)]

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/LogMoment.lean. -/
section

open MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An exponential upper tail turns a large event-restricted first moment into an
exponentially small event.  The constants are normalized for the tail
`μ {ω | s < Y ω} ≤ exp (-s / 2)`.

The integral hypothesis is stated in `ℝ≥0∞`, so it remains useful before integrability of
`Y` has been established. -/
theorem measure_event_le_two_mul_exp_neg_quarter_of_le_logMoment
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (E : Set Ω) (t : ℝ)
    (hY : Measurable Y) (hY_nonneg : ∀ ω, 0 ≤ Y ω) (hE : MeasurableSet E)
    (ht : 4 ≤ t)
    (htail : ∀ s : ℝ, 0 ≤ s →
      μ {ω | s < Y ω} ≤ ENNReal.ofReal (Real.exp (-s / 2)))
    (hmoment : ENNReal.ofReal t * μ E ≤
      ∫⁻ ω in E, ENNReal.ofReal (Y ω) ∂μ) :
    μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) := by
  let u := t / 2
  let Z : Ω → ℝ := fun ω ↦ max (Y ω - u) 0
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hZ_nonneg : ∀ ω, 0 ≤ Z ω := fun ω ↦ by simp [Z]
  have hZ : Measurable Z := by
    exact (hY.sub measurable_const).max measurable_const
  have hpoint : ∀ ω, ENNReal.ofReal (Y ω) ≤
      ENNReal.ofReal u + ENNReal.ofReal (Z ω) := by
    intro ω
    rw [← ENNReal.ofReal_add hu (hZ_nonneg ω)]
    apply ENNReal.ofReal_le_ofReal
    dsimp [Z]
    by_cases h : Y ω ≤ u
    · simp [h, hY_nonneg ω]
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      linarith
  have hmoment_upper : (∫⁻ ω in E, ENNReal.ofReal (Y ω) ∂μ) ≤
      ENNReal.ofReal u * μ E + ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ := by
    calc
      (∫⁻ ω in E, ENNReal.ofReal (Y ω) ∂μ) ≤
          ∫⁻ ω in E, (ENNReal.ofReal u + ENNReal.ofReal (Z ω)) ∂μ :=
        setLIntegral_mono' hE fun ω _ ↦ hpoint ω
      _ = ENNReal.ofReal u * μ E + ∫⁻ ω in E, ENNReal.ofReal (Z ω) ∂μ := by
        rw [lintegral_add_left measurable_const]
        simp
      _ ≤ ENNReal.ofReal u * μ E + ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ := by
        exact add_le_add_right
          (setLIntegral_le_lintegral E (fun ω ↦ ENNReal.ofReal (Z ω))) _
  have htail_Z : ∀ s : ℝ, 0 < s →
      μ {ω | s < Z ω} ≤ ENNReal.ofReal (Real.exp (-(s + u) / 2)) := by
    intro s hs
    have hsets : {ω | s < Z ω} = {ω | s + u < Y ω} := by
      ext ω
      simp only [Z, mem_setOf_eq]
      rw [lt_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h
        left
        linarith
    rw [hsets]
    exact htail (s + u) (by linarith)
  have hZ_lintegral : (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) ≤
      ENNReal.ofReal (2 * Real.exp (-u / 2)) := by
    rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hZ_nonneg) hZ.aemeasurable]
    have hexp_eq : (fun s : ℝ ↦ Real.exp (-(s + u) / 2)) =
        fun s ↦ Real.exp (-u / 2) * Real.exp (-(1 / 2) * s) := by
      funext s
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp_integrable : Integrable (fun s : ℝ ↦ Real.exp (-(s + u) / 2))
        (volume.restrict (Ioi 0)) := by
      rw [hexp_eq]
      exact (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).const_mul _
    have hexp_integral : (∫ s : ℝ in Ioi 0, Real.exp (-(s + u) / 2)) =
        2 * Real.exp (-u / 2) := by
      rw [hexp_eq, integral_const_mul,
        integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
      norm_num
      ring
    calc
      (∫⁻ s in Ioi 0, μ {ω | s < Z ω} ∂volume) ≤
          ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-(s + u) / 2)) ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro s hs
        exact htail_Z s hs
      _ = ENNReal.ofReal (2 * Real.exp (-u / 2)) := by
        calc
          (∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-(s + u) / 2)) ∂volume) =
              ENNReal.ofReal (∫ s : ℝ in Ioi 0, Real.exp (-(s + u) / 2)) :=
            (ofReal_integral_eq_lintegral_ofReal hexp_integrable
              (Filter.Eventually.of_forall fun _ ↦ Real.exp_nonneg _)).symm
          _ = ENNReal.ofReal (2 * Real.exp (-u / 2)) := congrArg ENNReal.ofReal hexp_integral
  have hmain : ENNReal.ofReal t * μ E ≤
      ENNReal.ofReal u * μ E + ENNReal.ofReal (2 * Real.exp (-u / 2)) :=
    hmoment.trans (hmoment_upper.trans (by gcongr))
  have hhalf : ENNReal.ofReal u * μ E ≤
      ENNReal.ofReal (2 * Real.exp (-u / 2)) := by
    have ht_eq : ENNReal.ofReal t = ENNReal.ofReal u + ENNReal.ofReal u := by
      rw [← ENNReal.ofReal_add hu hu]
      congr 1
      dsimp [u]
      ring
    rw [ht_eq, add_mul] at hmain
    exact ENNReal.le_of_add_le_add_left (by finiteness) hmain
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have hprob : μ E ≤ ENNReal.ofReal ((2 * Real.exp (-u / 2)) / u) := by
    rw [ENNReal.ofReal_div_of_pos hu_pos]
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.2 hu_pos).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 <| by
      simpa [mul_comm] using hhalf
  calc
    μ E ≤ ENNReal.ofReal ((2 * Real.exp (-u / 2)) / u) := hprob
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) := by
      apply ENNReal.ofReal_le_ofReal
      have hu_one : 1 ≤ u := by
        calc
          (1 : ℝ) ≤ 2 := by norm_num
          _ ≤ u := by dsimp [u]; linarith
      have hnum_nonneg : 0 ≤ 2 * Real.exp (-u / 2) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      have hexp_arg : -u / 2 = -t / 4 := by
        dsimp [u]
        ring
      calc
        (2 * Real.exp (-u / 2)) / u ≤ 2 * Real.exp (-u / 2) :=
          div_le_self hnum_nonneg hu_one
        _ = 2 * Real.exp (-t / 4) := by rw [hexp_arg]

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/CircleLogTail.lean. -/
section

open MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalized average of `Y` over one angular period. -/
noncomputable def circleLogAverage (Y : Ω → ℝ → ℝ) (ω : Ω) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, Y ω θ

/-- Joint measurability makes the circle average measurable. -/
theorem measurable_circleLogAverage
    (Y : Ω → ℝ → ℝ) (hY : Measurable (Function.uncurry Y)) :
    Measurable (circleLogAverage Y) := by
  have hsection : StronglyMeasurable
      (fun ω ↦ ∫ θ : ℝ, Y ω θ ∂(volume.restrict (Ioc 0 (2 * Real.pi)))) :=
    hY.stronglyMeasurable.integral_prod_right
  have havg : circleLogAverage Y = fun ω ↦
      (2 * Real.pi)⁻¹ * ∫ θ : ℝ, Y ω θ ∂(volume.restrict (Ioc 0 (2 * Real.pi))) := by
    funext ω
    rw [circleLogAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rw [havg]
  exact hsection.measurable.const_mul _

/-- A pointwise exponential tail, uniformly in the angular parameter, gives an
exponential tail for the circle average. -/
theorem measure_event_le_two_mul_exp_neg_eighth_of_circleLogAverage
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → ℝ)
    (E : Set Ω) (t : ℝ)
    (hY : Measurable (Function.uncurry Y))
    (hY_nonneg : ∀ ω θ, 0 ≤ Y ω θ)
    (hY_int : Integrable (Function.uncurry Y)
      (μ.prod (volume.restrict (Ioc 0 (2 * Real.pi)))))
    (hE : MeasurableSet E)
    (ht : 8 ≤ t)
    (hE_large : E ⊆ {ω | t ≤ circleLogAverage Y ω})
    (htail : ∀ θ s : ℝ, 0 ≤ s →
      μ {ω | s < Y ω θ} ≤ ENNReal.ofReal (Real.exp (-s / 2))) :
    μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 8)) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  have hY_int_ν : Integrable (Function.uncurry Y) (μ.prod ν) := by
    simpa only [ν] using hY_int
  let F : Ω → ℝ → ℝ := fun ω θ ↦ E.indicator (fun ω ↦ Y ω θ) ω
  have hF_int : Integrable (Function.uncurry F) (μ.prod ν) := by
    have hpre : MeasurableSet (Prod.fst ⁻¹' E : Set (Ω × ℝ)) :=
      hE.preimage measurable_fst
    have heq : Function.uncurry F =
        (Prod.fst ⁻¹' E).indicator (Function.uncurry Y) := by
      funext z
      by_cases hz : z.1 ∈ E <;> simp [F, Function.uncurry, hz]
    rw [heq]
    exact hY_int_ν.indicator hpre
  have hν_real : ν.real univ = 2 * Real.pi := by
    simp [ν, Real.volume_real_Ioc_of_le Real.two_pi_pos.le]
  have hν_ne : ν ≠ 0 := by
    intro hν
    have : ν.real univ = 0 := by rw [hν]; simp
    rw [hν_real] at this
    exact (ne_of_gt Real.two_pi_pos) this
  let g : ℝ → ℝ := fun θ ↦ ∫ ω : Ω in E, Y ω θ ∂μ
  have hg_int : Integrable g ν := by
    have hinner : Integrable (fun θ ↦ ∫ ω : Ω, F ω θ ∂μ) ν := by
      simpa only [Function.uncurry_apply_pair] using hF_int.integral_prod_right
    have heq : (fun θ ↦ ∫ ω : Ω, F ω θ ∂μ) = g := by
      funext θ
      change (∫ ω : Ω, E.indicator (fun ω ↦ Y ω θ) ω ∂μ) =
        ∫ ω : Ω in E, Y ω θ ∂μ
      exact integral_indicator hE
    rw [← heq]
    exact hinner
  have hswap :
      (∫ ω : Ω in E, ∫ θ : ℝ, Y ω θ ∂ν ∂μ) = ∫ θ : ℝ, g θ ∂ν := by
    calc
      (∫ ω : Ω in E, ∫ θ : ℝ, Y ω θ ∂ν ∂μ) =
          ∫ ω : Ω, ∫ θ : ℝ, F ω θ ∂ν ∂μ := by
        simpa only [F] using (integral_integral_indicator Y hE).symm
      _ = ∫ θ : ℝ, ∫ ω : Ω, F ω θ ∂μ ∂ν :=
        integral_integral_swap hF_int
      _ = ∫ θ : ℝ, g θ ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with θ
        change (∫ ω : Ω, E.indicator (fun ω ↦ Y ω θ) ω ∂μ) =
          ∫ ω : Ω in E, Y ω θ ∂μ
        exact integral_indicator hE
  have hset_average :
      (∫ ω : Ω in E, circleLogAverage Y ω ∂μ) = ⨍ θ : ℝ, g θ ∂ν := by
    calc
      (∫ ω : Ω in E, circleLogAverage Y ω ∂μ) =
          (2 * Real.pi)⁻¹ * ∫ ω : Ω in E, ∫ θ : ℝ, Y ω θ ∂ν ∂μ := by
        simp only [circleLogAverage, ν,
          intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_const_mul]
      _ = (2 * Real.pi)⁻¹ * ∫ θ : ℝ, g θ ∂ν := by rw [hswap]
      _ = ⨍ θ : ℝ, g θ ∂ν := by
        rw [average_eq, hν_real, smul_eq_mul]
  have hA_int : Integrable (circleLogAverage Y) μ := by
    have hinner : Integrable (fun ω ↦ ∫ θ : ℝ, Y ω θ ∂ν) μ := by
      simpa only [Function.uncurry_apply_pair] using hY_int_ν.integral_prod_left
    have heq : circleLogAverage Y = fun ω ↦
        (2 * Real.pi)⁻¹ * ∫ θ : ℝ, Y ω θ ∂ν := by
      funext ω
      rw [circleLogAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rw [heq]
    exact hinner.const_mul _
  have hE_moment : t * μ.real E ≤ ∫ ω : Ω in E, circleLogAverage Y ω ∂μ :=
    setIntegral_ge_of_const_le_real hE (measure_ne_top μ E)
      (fun ω hω ↦ hE_large hω) hA_int.integrableOn
  have hsections_ae : ∀ᵐ θ ∂ν, Integrable (fun ω ↦ F ω θ) μ := by
    simpa only [Function.uncurry_apply_pair] using hF_int.prod_left_ae
  have hbad : ν {θ | ¬Integrable (fun ω ↦ F ω θ) μ} = 0 :=
    ae_iff.mp hsections_ae
  obtain ⟨θ, hθ_good, hθ_large⟩ :=
    exists_notMem_null_average_le hν_ne hg_int hbad
  have hFθ_int : Integrable (fun ω ↦ F ω θ) μ := by
    simpa only [mem_setOf_eq, not_not] using hθ_good
  have hYθ_int : IntegrableOn (fun ω ↦ Y ω θ) E μ := by
    apply (integrable_indicator_iff hE).mp
    simpa only [F] using hFθ_int
  have hreal_moment : t * μ.real E ≤ ∫ ω : Ω in E, Y ω θ ∂μ := by
    calc
      t * μ.real E ≤ ∫ ω : Ω in E, circleLogAverage Y ω ∂μ := hE_moment
      _ = ⨍ θ : ℝ, g θ ∂ν := hset_average
      _ ≤ g θ := hθ_large
      _ = ∫ ω : Ω in E, Y ω θ ∂μ := rfl
  have ht_nonneg : 0 ≤ t := by linarith
  have hmoment : ENNReal.ofReal t * μ E ≤
      ∫⁻ ω : Ω in E, ENNReal.ofReal (Y ω θ) ∂μ := by
    calc
      ENNReal.ofReal t * μ E = ENNReal.ofReal (t * μ.real E) := by
        rw [ENNReal.ofReal_mul ht_nonneg, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (∫ ω : Ω in E, Y ω θ ∂μ) :=
        ENNReal.ofReal_le_ofReal hreal_moment
      _ = ∫⁻ ω : Ω in E, ENNReal.ofReal (Y ω θ) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hYθ_int
          (Filter.Eventually.of_forall fun ω ↦ hY_nonneg ω θ)
  have hstrong : μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) :=
    measure_event_le_two_mul_exp_neg_quarter_of_le_logMoment μ (fun ω ↦ Y ω θ) E t
      (hY.comp measurable_prodMk_right) (fun ω ↦ hY_nonneg ω θ) hE (by linarith)
      (htail θ) hmoment
  calc
    μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) := hstrong
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t / 8)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith)) (by norm_num)

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/CircleNormGap.lean. -/
section

open Complex Function MeasureTheory Metric Real Set

namespace CofiniteDerivatives

/-- The excess of the circular average of the norm over the norm at the center. -/
noncomputable def normCircleGap (c : ℂ) (r : ℝ) : ℝ :=
  circleAverage (fun z : ℂ ↦ ‖z‖) c r - ‖c‖

/-- The norm pulled back along a parametrized circle is continuous. -/
theorem continuous_norm_circleMap (c : ℂ) (r : ℝ) :
    Continuous (fun θ : ℝ ↦ ‖circleMap c r θ‖) :=
  continuous_norm.comp (continuous_circleMap c r)

/-- The norm pulled back along a parametrized circle is measurable. -/
theorem measurable_norm_circleMap (c : ℂ) (r : ℝ) :
    Measurable (fun θ : ℝ ↦ ‖circleMap c r θ‖) :=
  (continuous_norm_circleMap c r).measurable

/-- The norm is integrable on every parametrized circle. -/
theorem circleIntegrable_norm (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z : ℂ ↦ ‖z‖) c r :=
  continuous_norm.continuousOn.circleIntegrable'

/-- Multiplying the norm by a real scalar commutes with circular averaging. -/
theorem circleAverage_mul_norm (a : ℝ) (c : ℂ) (r : ℝ) :
    circleAverage (fun z : ℂ ↦ a * ‖z‖) c r =
      a * circleAverage (fun z : ℂ ↦ ‖z‖) c r := by
  simpa only [smul_eq_mul] using
    (circleAverage_fun_smul (a := a) (f := fun z : ℂ ↦ ‖z‖) (c := c) (R := r))

/-- The centered circular norm statistic commutes with multiplication by a scalar. -/
theorem circleAverage_mul_norm_sub (a : ℝ) (c : ℂ) (r : ℝ) :
    circleAverage (fun z : ℂ ↦ a * ‖z‖) c r - a * ‖c‖ =
      a * normCircleGap c r := by
  rw [circleAverage_mul_norm]
  simp only [normCircleGap]
  ring

private theorem circleMap_add_antipode (c : ℂ) (r θ : ℝ) :
    circleMap c r θ + circleMap c r (θ + π) = 2 * c := by
  simp [circleMap, add_mul, Complex.exp_add]
  ring

private theorem norm_antipodal_pair_le (c : ℂ) (r θ : ℝ) :
    2 * ‖c‖ ≤ ‖circleMap c r θ‖ + ‖circleMap c r (θ + π)‖ := by
  calc
    2 * ‖c‖ = ‖(2 : ℂ) * c‖ := by simp
    _ = ‖circleMap c r θ + circleMap c r (θ + π)‖ := by
      rw [circleMap_add_antipode]
    _ ≤ ‖circleMap c r θ‖ + ‖circleMap c r (θ + π)‖ := norm_add_le _ _

private theorem exists_norm_antipodal_pair_lt (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ θ ∈ Icc 0 (2 * π),
      2 * ‖c‖ < ‖circleMap c r θ‖ + ‖circleMap c r (θ + π)‖ := by
  by_cases hc : c = 0
  · refine ⟨0, ⟨le_rfl, Real.two_pi_pos.le⟩, ?_⟩
    subst c
    simpa [circleMap, abs_of_pos hr] using
      (mul_pos (show (0 : ℝ) < 2 by norm_num) hr)
  · let u : ℂ := (r / ‖c‖ : ℝ) * I * c
    have hu_norm : ‖u‖ = r := by
      simp [u, abs_of_pos hr, hc]
    have hu_mem : u ∈ sphere (0 : ℂ) |r| := by
      simp [hu_norm, abs_of_pos hr]
    rw [← image_circleMap_Ioc] at hu_mem
    obtain ⟨θ, hθ, hcircle⟩ := hu_mem
    refine ⟨θ, ⟨hθ.1.le, hθ.2⟩, ?_⟩
    let x := circleMap c r θ
    let y := circleMap c r (θ + π)
    have hx : x = c + u := by
      calc
        x = c + circleMap 0 r θ := by simp [x, circleMap]
        _ = c + u := by rw [hcircle]
    have hy : y = c - u := by
      have hantipode : circleMap 0 r (θ + π) = -circleMap 0 r θ := by
        simp [circleMap, add_mul, Complex.exp_add]
      calc
        y = c + circleMap 0 r (θ + π) := by simp [y, circleMap]
        _ = c - u := by rw [hantipode, hcircle]; ring
    let a : ℝ := r / ‖c‖
    have hx_factor : x = (1 + (a : ℂ) * I) * c := by
      rw [hx]
      simp only [u, a]
      push_cast
      ring
    have hy_factor : y = (1 - (a : ℂ) * I) * c := by
      rw [hy]
      simp only [u, a]
      push_cast
      ring
    have hfactor_norm : ‖(1 : ℂ) + (a : ℂ) * I‖ = ‖(1 : ℂ) - (a : ℂ) * I‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
    have hnorm : ‖x‖ = ‖y‖ := by
      rw [hx_factor, hy_factor, norm_mul, norm_mul, hfactor_norm]
    have hxy_ne : x ≠ y := by
      rw [hx, hy]
      intro h
      have : u = 0 := by linear_combination h / 2
      exact hr.ne' (hu_norm ▸ norm_eq_zero.mpr this)
    have hstrict : ‖x + y‖ < ‖x‖ + ‖y‖ := by
      apply lt_of_le_of_ne (norm_add_le x y)
      intro hEq
      exact hxy_ne (eq_of_norm_eq_of_norm_add_eq hnorm hEq)
    have hsum : x + y = 2 * c := by
      exact circleMap_add_antipode c r θ
    rw [hsum, norm_mul, Complex.norm_ofNat] at hstrict
    exact hstrict

/-- The circular average of the norm is strictly larger than the norm at the center when the
radius is positive. -/
theorem normCircleGap_pos (c : ℂ) {r : ℝ} (hr : 0 < r) : 0 < normCircleGap c r := by
  let f : ℝ → ℝ := fun θ ↦ ‖circleMap c r θ‖
  let g : ℝ → ℝ := fun θ ↦ f θ + f (θ + π)
  have hf_cont : Continuous f := continuous_norm_circleMap c r
  have hg_cont : Continuous g := hf_cont.add (hf_cont.comp (continuous_id.add continuous_const))
  have hconst_lt :
      (∫ _θ : ℝ in 0..2 * π, 2 * ‖c‖) < ∫ θ : ℝ in 0..2 * π, g θ := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      Real.two_pi_pos continuousOn_const hg_cont.continuousOn
    · intro θ _
      exact norm_antipodal_pair_le c r θ
    · simpa only [g, f] using exists_norm_antipodal_pair_lt c r hr
  have hf_periodic : Periodic f (2 * π) := fun θ ↦ by
    simp only [f, periodic_circleMap c r θ]
  have hshift : (∫ θ : ℝ in 0..2 * π, f (θ + π)) = ∫ θ : ℝ in 0..2 * π, f θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa [add_assoc, add_comm, add_left_comm] using
      hf_periodic.intervalIntegral_add_eq π 0
  have hf_int : IntervalIntegrable f volume 0 (2 * π) :=
    hf_cont.intervalIntegrable _ _
  have hshift_int : IntervalIntegrable (fun θ ↦ f (θ + π)) volume 0 (2 * π) :=
    (hf_cont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hg_integral :
      (∫ θ : ℝ in 0..2 * π, g θ) =
        (∫ θ : ℝ in 0..2 * π, f θ) + ∫ θ : ℝ in 0..2 * π, f (θ + π) := by
    dsimp only [g]
    exact intervalIntegral.integral_add hf_int hshift_int
  have hintegral_lt : (2 * π) * (2 * ‖c‖) < 2 * ∫ θ : ℝ in 0..2 * π, f θ := by
    calc
      (2 * π) * (2 * ‖c‖) = ∫ _θ : ℝ in 0..2 * π, 2 * ‖c‖ := by
        simp [smul_eq_mul]
        ring
      _ < ∫ θ : ℝ in 0..2 * π, g θ := hconst_lt
      _ = (∫ θ : ℝ in 0..2 * π, f θ) + ∫ θ : ℝ in 0..2 * π, f θ := by
        rw [hg_integral, hshift]
      _ = 2 * ∫ θ : ℝ in 0..2 * π, f θ := by ring
  have hbase_lt :
      (2 * π) * ‖c‖ < ∫ θ : ℝ in 0..2 * π, f θ := by
    nlinarith [hintegral_lt]
  rw [normCircleGap, circleAverage_def, smul_eq_mul, sub_pos]
  change ‖c‖ < (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, f θ
  calc
    ‖c‖ = (2 * π)⁻¹ * ((2 * π) * ‖c‖) := by
      field_simp [ne_of_gt Real.two_pi_pos]
    _ < (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, f θ :=
      mul_lt_mul_of_pos_left hbase_lt (inv_pos.mpr Real.two_pi_pos)

/-- A positive square-root factor preserves positivity of the norm circle gap. -/
theorem sqrt_mul_normCircleGap_pos (c : ℂ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    0 < √x * normCircleGap c r :=
  mul_pos (Real.sqrt_pos.2 hx) (normCircleGap_pos c hr)

/-- Natural-number specialization of `circleAverage_mul_norm_sub`. -/
theorem circleAverage_sqrt_nat_mul_norm_sub (n : ℕ) (c : ℂ) (r : ℝ) :
    circleAverage (fun z : ℂ ↦ √(n : ℝ) * ‖z‖) c r - √(n : ℝ) * ‖c‖ =
      √(n : ℝ) * normCircleGap c r :=
  circleAverage_mul_norm_sub _ c r

/-- Multiplication by `sqrt n` preserves strict positivity for nonzero natural `n`. -/
theorem sqrt_nat_mul_normCircleGap_pos {n : ℕ} (hn : n ≠ 0) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < √(n : ℝ) * normCircleGap c r :=
  sqrt_mul_normCircleGap_pos c hr (by exact_mod_cast Nat.pos_of_ne_zero hn)

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/Jensen.lean. -/
section

open Metric Real Set

namespace CofiniteDerivatives

/-- The Jensen boundary-minus-center logarithmic statistic for a disk. -/
noncomputable def diskLogStat (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
  circleAverage (fun z ↦ Real.log ‖f z‖) c r - Real.log ‖f c‖

/-- A zero-free analytic function has vanishing Jensen statistic. This is the deterministic bridge
from a hole event to a deviation event; no zero-counting measurability is needed. -/
theorem diskLogStat_eq_zero_of_zeroFree {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c |r|))
    (hzero : ∀ z ∈ closedBall c |r|, f z ≠ 0) :
    diskLogStat f c r = 0 := by
  rw [diskLogStat, hf.circleAverage_log_norm_of_ne_zero hzero, sub_self]

/-- Entire sample paths satisfy the analytic hypothesis in the hole-to-deviation bridge. -/
theorem diskLogStat_eq_zero_of_entire_zeroFree {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hzero : ∀ z ∈ closedBall c |r|, f z ≠ 0) :
    diskLogStat f c r = 0 :=
  diskLogStat_eq_zero_of_zeroFree (hf.mono (by simp)) hzero

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/HoleBound.lean. -/
section

open Complex MeasureTheory Metric Real Set
open scoped ENNReal

namespace CofiniteDerivatives

noncomputable section

/-- The deterministic compact-error bound at the center of a disk. -/
def centerUpperConstant (c : ℂ) : ℝ :=
  (‖c‖ + ‖c‖ ^ 2) / 2

/-- The nonnegative logarithmic deficit at a fixed complex point. -/
def pointwiseLogDeficit (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) : ℝ :=
  max (pointwisePotential n z -
    Real.log ‖randomFockDeriv n ω z‖ - pointwiseSaddleLoss n) 0

/-- The sample-point pair obtained from a coefficient sequence and an angle. -/
def circleSampleMap (c : ℂ) (r : ℝ) (p : (ℕ → ℂ) × ℝ) : (ℕ → ℂ) × ℂ :=
  (p.1, circleMap c r p.2)

/-- The nonnegative logarithmic deficit on the circle centered at `c` with radius `r`. -/
def circleLogDeficit (n : ℕ) (c : ℂ) (r : ℝ) (ω : ℕ → ℂ) (θ : ℝ) : ℝ :=
  pointwiseLogDeficit n ω (circleMap c r θ)

theorem measurable_pointwisePotential (n : ℕ) : Measurable (pointwisePotential n) := by
  unfold pointwisePotential
  exact measurable_const.add (measurable_id.norm.mul_const (Real.sqrt n))

theorem measurable_pointwiseLogDeficit (n : ℕ) :
    Measurable (fun p : (ℕ → ℂ) × ℂ ↦ pointwiseLogDeficit n p.1 p.2) := by
  unfold pointwiseLogDeficit
  have hpotential : Measurable (fun p : (ℕ → ℂ) × ℂ ↦ pointwisePotential n p.2) :=
    (measurable_pointwisePotential n).comp measurable_snd
  exact ((hpotential.sub (measurable_randomFockDeriv n).norm.log).sub measurable_const).max
    measurable_const

theorem measurable_circleSampleMap (c : ℂ) (r : ℝ) : Measurable (circleSampleMap c r) := by
  have hfst : Measurable (fun p : (ℕ → ℂ) × ℝ ↦ p.1) := measurable_fst
  exact Measurable.prodMk hfst ((measurable_circleMap c r).comp measurable_snd)

/-- The circle logarithmic deficit is jointly measurable in the sample and angle. -/
theorem measurable_circleLogDeficit (n : ℕ) (c : ℂ) (r : ℝ) :
    Measurable (fun p : (ℕ → ℂ) × ℝ ↦ circleLogDeficit n c r p.1 p.2) := by
  change Measurable
    ((fun p : (ℕ → ℂ) × ℂ ↦ pointwiseLogDeficit n p.1 p.2) ∘ circleSampleMap c r)
  exact (measurable_pointwiseLogDeficit n).comp (measurable_circleSampleMap c r)

theorem circleLogDeficit_nonneg (n : ℕ) (c : ℂ) (r : ℝ) (ω : ℕ → ℂ) (θ : ℝ) :
    0 ≤ circleLogDeficit n c r ω θ :=
  le_max_right _ _

/-- On a saddle-ready circle, every angular section has the exponential tail used by
`measure_event_le_two_mul_exp_neg_eighth_of_circleLogAverage`. -/
theorem P_circleLogDeficit_tail
    (n : ℕ) (c : ℂ) (r δ M : ℝ)
    (hn : PointwiseSaddleReady n δ M)
    (hnorm : ∀ θ, δ ≤ ‖circleMap c r θ‖ ∧ ‖circleMap c r θ‖ ≤ M)
    (θ s : ℝ) (hs : 0 ≤ s) :
    P {ω | s < circleLogDeficit n c r ω θ} ≤
      ENNReal.ofReal (Real.exp (-s / 2)) := by
  let z := circleMap c r θ
  have hx : 1 ≤ ‖z‖ * Real.sqrt n :=
    hn.1.trans <| mul_le_mul_of_nonneg_right (hnorm θ).1 (Real.sqrt_nonneg _)
  have hzn : ‖z‖ ≤ Real.sqrt n := (hnorm θ).2.trans hn.2
  have hset : {ω | s < circleLogDeficit n c r ω θ} =
      {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} := by
    ext ω
    change s < max
      (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ -
        pointwiseSaddleLoss n) 0 ↔ _
    simp only [lt_max_iff]
    constructor
    · rintro (h | h)
      · exact lt_sub_iff_add_lt.mp h
      · exact (not_lt_of_ge hs h).elim
    · intro h
      exact Or.inl (lt_sub_iff_add_lt.mpr h)
  rw [hset]
  calc
    P {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} ≤ ENNReal.ofReal (Real.exp (-2 * s)) :=
      P_pointwise_log_lowerTail n z s hx hzn
    _ ≤ ENNReal.ofReal (Real.exp (-s / 2)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_monotone (by linarith)

/-- The uniform exponential section tail makes the circle deficit integrable under the
product of the coefficient law and angular volume. -/
theorem integrable_circleLogDeficit
    (n : ℕ) (c : ℂ) (r δ M : ℝ)
    (hn : PointwiseSaddleReady n δ M)
    (hnorm : ∀ θ, δ ≤ ‖circleMap c r θ‖ ∧ ‖circleMap c r θ‖ ≤ M) :
    Integrable (Function.uncurry (circleLogDeficit n c r))
      (P.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let Y : (ℕ → ℂ) × ℝ → ℝ := Function.uncurry (circleLogDeficit n c r)
  have hY : Measurable Y := measurable_circleLogDeficit n c r
  have hY_nonneg : ∀ p, 0 ≤ Y p := fun p ↦ circleLogDeficit_nonneg n c r p.1 p.2
  have hlintegral : (∫⁻ p, ENNReal.ofReal (Y p) ∂P.prod ν) < ∞ := by
    rw [lintegral_eq_lintegral_meas_lt (P.prod ν)
      (Filter.Eventually.of_forall hY_nonneg) hY.aemeasurable]
    have hlevel (s : ℝ) (hs : s ∈ Ioi 0) :
        P.prod ν {p | s < Y p} ≤
          ENNReal.ofReal (Real.exp (-s / 2)) * ν univ := by
      have hset : MeasurableSet {p | s < Y p} :=
        measurableSet_lt measurable_const hY
      rw [Measure.prod_apply_symm hset]
      calc
        (∫⁻ θ, P ((fun ω ↦ (ω, θ)) ⁻¹' {p | s < Y p}) ∂ν) ≤
            ∫⁻ _θ, ENNReal.ofReal (Real.exp (-s / 2)) ∂ν := by
          apply lintegral_mono
          intro θ
          change P {ω | s < circleLogDeficit n c r ω θ} ≤ _
          exact P_circleLogDeficit_tail n c r δ M hn hnorm θ s hs.le
        _ = ENNReal.ofReal (Real.exp (-s / 2)) * ν univ :=
          lintegral_const _
    calc
      (∫⁻ s in Ioi 0, P.prod ν {p | s < Y p} ∂volume) ≤
          ∫⁻ s in Ioi 0,
            ENNReal.ofReal (Real.exp (-s / 2)) * ν univ ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro s hs
        exact hlevel s hs
      _ = (∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s / 2)) ∂volume) * ν univ := by
        exact lintegral_mul_const' (ν univ)
          (fun s ↦ ENNReal.ofReal (Real.exp (-s / 2))) (measure_ne_top ν univ)
      _ < ∞ := by
        have hexp_int : Integrable (fun s : ℝ ↦ Real.exp (-s / 2))
            (volume.restrict (Ioi 0)) := by
          apply (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0).congr
          filter_upwards [] with s
          congr 1
          ring
        have hexp_lt :
            (∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s / 2)) ∂volume) < ∞ := by
          exact hexp_int.lintegral_lt_top
        exact ENNReal.mul_lt_top hexp_lt (measure_lt_top ν univ)
  refine ⟨hY.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hY_nonneg)]
  exact hlintegral

/-- The deterministic pointwise potential gains exactly `sqrt n` times the norm circle gap. -/
theorem circleAverage_pointwisePotential_sub_center (n : ℕ) (c : ℂ) (r : ℝ) :
    circleAverage (pointwisePotential n) c r - pointwisePotential n c =
      Real.sqrt n * normCircleGap c r := by
  have hnorm : CircleIntegrable (fun z : ℂ ↦ ‖z‖ * Real.sqrt n) c r := by
    simpa only [smul_eq_mul, mul_comm] using
      (circleIntegrable_norm c r).const_fun_smul (a := Real.sqrt n)
  have hmul : circleAverage (fun z : ℂ ↦ ‖z‖ * Real.sqrt n) c r =
      Real.sqrt n * circleAverage (fun z : ℂ ↦ ‖z‖) c r := by
    simpa only [mul_comm] using circleAverage_mul_norm (Real.sqrt n) c r
  rw [show pointwisePotential n = fun z : ℂ ↦
      Real.log (Real.sqrt (Nat.factorial n : ℝ)) + ‖z‖ * Real.sqrt n by
    rfl]
  rw [circleAverage_fun_add (circleIntegrable_const _ c r) hnorm,
    circleAverage_const, hmul]
  simp only [normCircleGap]
  ring

/-- Every sample path obeys the compact deterministic logarithmic upper bound at the center. -/
theorem log_norm_randomFockDeriv_sub_pointwisePotential_le_centerUpperConstant
    (n : ℕ) (ω : ℕ → ℂ) (c : ℂ) (hn : n ≠ 0) :
    Real.log ‖randomFockDeriv n ω c‖ - pointwisePotential n c ≤
      centerUpperConstant c := by
  simpa only [randomFockDeriv, randomFock, centerUpperConstant] using
    log_norm_iteratedDeriv_fockFunction_sub_potential_le
      (fun k ↦ clipDisk (ω k)) (fun k ↦ norm_clipDisk_le_one (ω k))
      n c ‖c‖ hn le_rfl

/-- For every sample path, the angular logarithmic deficit is interval-integrable. -/
theorem intervalIntegrable_circleLogDeficit
    (n : ℕ) (c : ℂ) (r : ℝ) (ω : ℕ → ℂ) :
    IntervalIntegrable (circleLogDeficit n c r ω) volume 0 (2 * Real.pi) := by
  have hpotential : CircleIntegrable (pointwisePotential n) c r := by
    apply ContinuousOn.circleIntegrable'
    exact (continuous_const.add (continuous_norm.mul continuous_const)).continuousOn
  have hlog : CircleIntegrable
      (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r :=
    circleIntegrable_log_norm_meromorphicOn fun z _ ↦
      (analyticOnNhd_randomFockDeriv n ω).meromorphicOn z (by simp)
  have hraw : CircleIntegrable (fun z : ℂ ↦
      pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ -
        pointwiseSaddleLoss n) c r :=
    (hpotential.sub hlog).sub (circleIntegrable_const _ c r)
  have hmax : CircleIntegrable (fun z : ℂ ↦ max
      (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ -
        pointwiseSaddleLoss n) 0) c r :=
    ⟨hraw.1.sup integrableOn_zero, hraw.2.sup integrableOn_zero⟩
  change IntervalIntegrable (fun θ : ℝ ↦ max
    (pointwisePotential n (circleMap c r θ) -
      Real.log ‖randomFockDeriv n ω (circleMap c r θ)‖ -
      pointwiseSaddleLoss n) 0) volume 0 (2 * Real.pi)
  exact hmax

/-- The deterministic threshold for the large circle-average event. -/
def holeThreshold (n : ℕ) (c : ℂ) (r : ℝ) : ℝ :=
  Real.sqrt n * normCircleGap c r - centerUpperConstant c - pointwiseSaddleLoss n

/-- The event that the random derivative has no zero in the outer open disk. -/
def randomFockHoleEvent (n : ℕ) (c : ℂ) (R : ℝ) : Set (ℕ → ℂ) :=
  {ω | ∀ z ∈ ball c R, randomFockDeriv n ω z ≠ 0}

/-- The measurable event where the circle deficit average exceeds its deterministic threshold. -/
def largeCircleDeficitEvent (n : ℕ) (c : ℂ) (r : ℝ) : Set (ℕ → ℂ) :=
  {ω | holeThreshold n c r ≤ circleLogAverage (circleLogDeficit n c r) ω}

theorem measurableSet_largeCircleDeficitEvent (n : ℕ) (c : ℂ) (r : ℝ) :
    MeasurableSet (largeCircleDeficitEvent n c r) := by
  exact measurableSet_le measurable_const
    (measurable_circleLogAverage _ (measurable_circleLogDeficit n c r))

/-- A zero-free outer disk forces a large average logarithmic deficit on every enclosed circle. -/
theorem holeEvent_subset_largeCircleDeficitEvent
    (n : ℕ) (c : ℂ) {r R : ℝ} (hr : 0 < r)
    (hclosed : closedBall c r ⊆ ball c R) (hn : n ≠ 0) :
    randomFockHoleEvent n c R ⊆ largeCircleDeficitEvent n c r := by
  intro ω hω
  have hzero : ∀ z ∈ closedBall c |r|, randomFockDeriv n ω z ≠ 0 := by
    intro z hz
    apply hω z
    apply hclosed
    simpa only [abs_of_pos hr] using hz
  have hJensen : diskLogStat (randomFockDeriv n ω) c r = 0 :=
    diskLogStat_eq_zero_of_entire_zeroFree
      (analyticOnNhd_randomFockDeriv n ω) hzero
  have hlog_average :
      circleAverage (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r =
        Real.log ‖randomFockDeriv n ω c‖ := by
    simpa only [diskLogStat, sub_eq_zero] using hJensen
  let raw : ℂ → ℝ := fun z ↦
    pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ - pointwiseSaddleLoss n
  let positive : ℂ → ℝ := fun z ↦ max (raw z) 0
  have hpotential : CircleIntegrable (pointwisePotential n) c r := by
    apply ContinuousOn.circleIntegrable'
    exact (continuous_const.add (continuous_norm.mul continuous_const)).continuousOn
  have hlog : CircleIntegrable
      (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r :=
    circleIntegrable_log_norm_meromorphicOn fun z _ ↦
      (analyticOnNhd_randomFockDeriv n ω).meromorphicOn z (by simp)
  have hdiff : CircleIntegrable (fun z : ℂ ↦
      pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖) c r := by
    exact hpotential.sub hlog
  have hraw : CircleIntegrable raw c r := by
    exact hdiff.sub (circleIntegrable_const _ c r)
  have hpositive : CircleIntegrable positive c r := by
    exact ⟨hraw.1.sup integrableOn_zero, hraw.2.sup integrableOn_zero⟩
  have hraw_average :
      circleAverage raw c r = circleAverage (pointwisePotential n) c r -
        circleAverage (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r -
          pointwiseSaddleLoss n := by
    calc
      circleAverage raw c r = circleAverage (fun z : ℂ ↦
          (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖) -
            pointwiseSaddleLoss n) c r := rfl
      _ = circleAverage (fun z : ℂ ↦
          pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖) c r -
            circleAverage (fun _ : ℂ ↦ pointwiseSaddleLoss n) c r :=
        circleAverage_fun_sub hdiff (circleIntegrable_const _ c r)
      _ = circleAverage (pointwisePotential n) c r -
          circleAverage (fun z : ℂ ↦ Real.log ‖randomFockDeriv n ω z‖) c r -
            pointwiseSaddleLoss n := by
        rw [circleAverage_fun_sub hpotential hlog, circleAverage_const]
  have hcenter :=
    log_norm_randomFockDeriv_sub_pointwisePotential_le_centerUpperConstant n ω c hn
  have ht_raw : holeThreshold n c r ≤ circleAverage raw c r := by
    rw [hraw_average, hlog_average]
    rw [holeThreshold, ← circleAverage_pointwisePotential_sub_center n c r]
    linarith
  have hraw_positive : circleAverage raw c r ≤ circleAverage positive c r := by
    apply circleAverage_mono hraw hpositive
    intro z _
    exact le_max_left _ _
  have hpositive_eq :
      circleAverage positive c r = circleLogAverage (circleLogDeficit n c r) ω := by
    rfl
  change holeThreshold n c r ≤ circleLogAverage (circleLogDeficit n c r) ω
  rw [← hpositive_eq]
  exact ht_raw.trans hraw_positive

/-- For a saddle-ready circle whose threshold is at least eight, the outer measure of the
zero-free outer-disk event has the exponential circle-log bound. -/
theorem P_outerMeasure_holeEvent_le_two_mul_exp_neg_eighth
    (n : ℕ) (c : ℂ) {r R δ M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hn : PointwiseSaddleReady n δ M)
    (hnorm : ∀ z ∈ sphere c r, δ ≤ ‖z‖ ∧ ‖z‖ ≤ M)
    (ht : 8 ≤ holeThreshold n c r) :
    P.toOuterMeasure (randomFockHoleEvent n c R) ≤
      ENNReal.ofReal (2 * Real.exp (-holeThreshold n c r / 8)) := by
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    norm_num [PointwiseSaddleReady] at hn
  have hcircle : ∀ θ, δ ≤ ‖circleMap c r θ‖ ∧ ‖circleMap c r θ‖ ≤ M := by
    intro θ
    exact hnorm (circleMap c r θ) (circleMap_mem_sphere c hr.le θ)
  have hlarge :
      P (largeCircleDeficitEvent n c r) ≤
        ENNReal.ofReal (2 * Real.exp (-holeThreshold n c r / 8)) := by
    apply measure_event_le_two_mul_exp_neg_eighth_of_circleLogAverage
      P (circleLogDeficit n c r) (largeCircleDeficitEvent n c r)
      (holeThreshold n c r)
    · exact measurable_circleLogDeficit n c r
    · exact circleLogDeficit_nonneg n c r
    · exact integrable_circleLogDeficit n c r δ M hn hcircle
    · exact measurableSet_largeCircleDeficitEvent n c r
    · exact ht
    · intro ω hω
      exact hω
    · exact P_circleLogDeficit_tail n c r δ M hn hcircle
  rw [Measure.toOuterMeasure_apply]
  exact (measure_mono
    (holeEvent_subset_largeCircleDeficitEvent n c hr
      (closedBall_subset_ball hrR) hn0)).trans hlarge

end

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/Summability.lean. -/
section

open Filter
open scoped ENNReal

namespace CofiniteDerivatives

/-- The logarithm of a natural number is eventually bounded by any positive multiple of its
square root. -/
theorem eventually_log_le_mul_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * Real.sqrt n := by
  have hlog_real : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ c * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlog_real,
    eventually_ge_atTop (1 : ℕ)] with n hn hnone
  rw [Real.sqrt_eq_rpow]
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnone)
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg hlog_nonneg, abs_of_nonneg hrpow_nonneg] at hn
  exact hn

/-- A stretched exponential with square-root exponent is summable on the natural numbers. -/
theorem summable_exp_neg_mul_sqrt {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * Real.sqrt n)) := by
  have hlog_nat : ∀ᶠ n : ℕ in atTop,
      2 * Real.log n ≤ c * Real.sqrt n := by
    filter_upwards [eventually_log_le_mul_sqrt (half_pos hc)] with n hn
    linarith
  have hle : ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * Real.sqrt n) ≤ (n : ℝ) ^ (-2 : ℝ) := by
    filter_upwards [hlog_nat, eventually_ge_atTop (1 : ℕ)] with n hn hnone
    calc
      Real.exp (-c * Real.sqrt n)
          ≤ Real.exp (-2 * Real.log n) := Real.exp_le_exp.mpr (by linarith)
      _ = (n : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_def_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hnone))]
        congr 1
        ring
  have hmajor : Summable (fun n : ℕ =>
      max (Real.exp (-c * Real.sqrt n)) ((n : ℝ) ^ (-2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).congr_atTop <|
      hle.mono fun _ hn => (max_eq_right hn).symm
  exact hmajor.of_nonneg_of_le (fun _ => Real.exp_nonneg _) fun _ => le_max_left _ _

/-- The corresponding nonnegative `ENNReal` series has finite total mass. -/
theorem ennreal_tsum_mul_exp_neg_mul_sqrt_ne_top {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    (∑' n : ℕ, ENNReal.ofReal (C * Real.exp (-c * Real.sqrt n))) ≠ ∞ := by
  have hsum : Summable (fun n : ℕ => C * Real.exp (-c * Real.sqrt n)) :=
    (summable_exp_neg_mul_sqrt hc).mul_left C
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg hC (Real.exp_nonneg _)) hsum]
  exact ENNReal.ofReal_ne_top

/-- For positive `a`, the square-root main term eventually absorbs the logarithmic and constant
losses in the threshold used for the tail estimate. -/
theorem eventually_half_mul_sqrt_le_threshold {a C0 : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      (a / 2) * Real.sqrt n ≤ a * Real.sqrt n - (2 + Real.log n / 2) - C0 := by
  have hlog : ∀ᶠ n : ℕ in atTop,
      Real.log n / 2 ≤ (a / 4) * Real.sqrt n := by
    filter_upwards [eventually_log_le_mul_sqrt (half_pos ha)] with n hn
    linarith
  have hsqrt : Tendsto (fun n : ℕ => (a / 4) * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  filter_upwards [hlog, hsqrt.eventually_ge_atTop (2 + C0)] with n hlogn hconstant
  linarith

/-- The shifted square-root/logarithm tail occurring in the application is summable; changing
finitely many initial terms is harmless. -/
theorem summable_exp_neg_sqrt_sub_log {a C0 : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ =>
      Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)) := by
  have hle : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8) ≤
        Real.exp (-(a / 16) * Real.sqrt n) := by
    filter_upwards [eventually_half_mul_sqrt_le_threshold (C0 := C0) ha] with n hn
    apply Real.exp_le_exp.mpr
    linarith
  have hmajor : Summable (fun n : ℕ =>
      max (Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8))
        (Real.exp (-(a / 16) * Real.sqrt n))) :=
    (summable_exp_neg_mul_sqrt (by positivity : 0 < a / 16)).congr_atTop <|
      hle.mono fun _ hn => (max_eq_right hn).symm
  exact hmajor.of_nonneg_of_le (fun _ => Real.exp_nonneg _) fun _ => le_max_left _ _

end CofiniteDerivatives
end

/-! Flattened from CofiniteDerivatives/Main.lean. -/
section

open Filter MeasureTheory Metric Set
open scoped ENNReal Polynomial

namespace CofiniteDerivatives

noncomputable section

private theorem eventually_disk_saddle_ready (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      PointwiseSaddleReady n (diskNormLower j) (diskNormUpper j) := by
  have hlower : 0 < diskNormLower j := diskNormLower_pos j
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_ge_atTop ((diskNormLower j)⁻¹),
    hsqrt.eventually_ge_atTop (diskNormUpper j)] with n hnLower hnUpper
  constructor
  · calc
      1 = diskNormLower j * (diskNormLower j)⁻¹ := by
        simp [ne_of_gt hlower]
      _ ≤ diskNormLower j * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hnLower hlower.le
  · exact hnUpper

private theorem eventually_holeThreshold_ge_eight (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      8 ≤ holeThreshold n (diskCenter j) (diskRadius j / 2) := by
  let a := normCircleGap (diskCenter j) (diskRadius j / 2)
  have hr : 0 < diskRadius j / 2 := half_pos (diskRadius_pos j)
  have ha : 0 < a := normCircleGap_pos (diskCenter j) hr
  have hmain := eventually_half_mul_sqrt_le_threshold
    (a := a) (C0 := centerUpperConstant (diskCenter j)) ha
  have hsqrt : Tendsto (fun n : ℕ => (a / 2) * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (half_pos ha)
  filter_upwards [hmain, hsqrt.eventually_ge_atTop 8] with n hn h8
  rw [holeThreshold]
  dsimp only [pointwiseSaddleLoss]
  nlinarith

private theorem randomFockDiskHole_subset (j n : ℕ) :
    randomFockDiskHole j n ⊆
      randomFockHoleEvent n (diskCenter j) (diskRadius j) := by
  intro ω hω z hz
  have hmiss : ¬(randomFockZeroSet ω n ∩ diskBasis j).Nonempty := by
    exact hω
  intro hzero
  apply hmiss
  exact ⟨z, hzero, by simpa [diskBasis] using hz⟩

private theorem eventually_randomFockDiskHole_measure_le (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      P (randomFockDiskHole j n) ≤
        ENNReal.ofReal
          (2 * Real.exp
            (-(normCircleGap (diskCenter j) (diskRadius j / 2) * Real.sqrt n -
              Real.log n / 2 -
              (centerUpperConstant (diskCenter j) + 2)) / 8)) := by
  filter_upwards [eventually_disk_saddle_ready j,
    eventually_holeThreshold_ge_eight j,
    eventually_ne_atTop 0] with n hsaddle hthreshold hn
  have hr : 0 < diskRadius j / 2 := half_pos (diskRadius_pos j)
  have hrR : diskRadius j / 2 < diskRadius j := by
    linarith [diskRadius_pos j]
  have hnorm : ∀ z ∈ sphere (diskCenter j) (diskRadius j / 2),
      diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j :=
    fun z hz => norm_mem_sphere_half_bounds j hz
  have houter := P_outerMeasure_holeEvent_le_two_mul_exp_neg_eighth
    n (diskCenter j) hr hrR hsaddle hnorm hthreshold
  have hmeasure : P (randomFockDiskHole j n) ≤
      P.toOuterMeasure (randomFockHoleEvent n (diskCenter j) (diskRadius j)) := by
    exact P.toOuterMeasure.mono (randomFockDiskHole_subset j n)
  calc
    P (randomFockDiskHole j n) ≤
        P.toOuterMeasure (randomFockHoleEvent n (diskCenter j) (diskRadius j)) := hmeasure
    _ ≤ ENNReal.ofReal (2 * Real.exp
          (-holeThreshold n (diskCenter j) (diskRadius j / 2) / 8)) := houter
    _ = ENNReal.ofReal
          (2 * Real.exp
            (-(normCircleGap (diskCenter j) (diskRadius j / 2) * Real.sqrt n -
              Real.log n / 2 -
              (centerUpperConstant (diskCenter j) + 2)) / 8)) := by
      congr 2
      rw [holeThreshold]
      simp only [pointwiseSaddleLoss]
      ring_nf

/-- For each rational basis disk, the probabilities that a derivative misses the disk have finite
sum. This is the final probabilistic input to Borel--Cantelli. -/
theorem randomFockDiskHole_tsum_lt_top (j : ℕ) :
    (∑' n, P (randomFockDiskHole j n)) < ∞ := by
  let a := normCircleGap (diskCenter j) (diskRadius j / 2)
  let C0 := centerUpperConstant (diskCenter j) + 2
  have hr : 0 < diskRadius j / 2 := half_pos (diskRadius_pos j)
  have ha : 0 < a := normCircleGap_pos (diskCenter j) hr
  have hreal : Summable (fun n : ℕ =>
      2 * Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)) :=
    (summable_exp_neg_sqrt_sub_log ha).mul_left 2
  have hbound : ∀ᶠ n : ℕ in atTop,
      P (randomFockDiskHole j n) ≤
        ENNReal.ofReal
          (2 * Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)) := by
    simpa only [a, C0] using eventually_randomFockDiskHole_measure_le j
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  let majorant : ℕ → ℝ := fun n =>
    if n < N then 1
    else 2 * Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)
  have hmajorant : Summable majorant := by
    apply hreal.congr_atTop
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [majorant, not_lt_of_ge hn]
  have hmajorant_nonneg : ∀ n, 0 ≤ majorant n := by
    intro n
    simp only [majorant]
    split_ifs
    · norm_num
    · positivity
  have hterm : ∀ n, P (randomFockDiskHole j n) ≤ ENNReal.ofReal (majorant n) := by
    intro n
    by_cases hn : n < N
    · simp only [majorant, if_pos hn, ENNReal.ofReal_one]
      exact (measure_mono (subset_univ _)).trans_eq measure_univ
    · simp only [majorant, if_neg hn]
      exact hN n (Nat.le_of_not_gt hn)
  exact (ENNReal.tsum_le_tsum hterm).trans_lt hmajorant.tsum_ofReal_lt_top

/-- There exists a nonpolynomial entire function whose sufficiently high derivatives have a zero
in every nonempty open subset of the complex plane. Equivalently, every strictly increasing
subsequence of derivative orders has zero sets with dense union. -/
theorem exists_transcendental_entire_with_cofinite_derivative_zeros :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      DerivativesCofinitelyHit f ∧
      EveryDerivativeSubsequenceDense f := by
  obtain ⟨ω, hentire, hnonpoly, hcofinite, hdense⟩ :=
    exists_randomFock_final_of_summable_holes
      (fun j => randomFockDiskHole_tsum_lt_top j)
  exact ⟨randomFock ω, hentire, hnonpoly, hcofinite, hdense⟩

/-- The bounded Fock witness also has an explicit quadratic exponential majorant. -/
theorem exists_transcendental_entire_with_cofinite_derivative_zeros_and_growth :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      DerivativesCofinitelyHit f ∧
      EveryDerivativeSubsequenceDense f ∧
      (∀ z : ℂ, ‖f z‖ ≤ Real.sqrt 2 * Real.exp (‖z‖ ^ 2)) := by
  obtain ⟨ω, hentire, hnonpoly, hcofinite, hdense⟩ :=
    exists_randomFock_final_of_summable_holes
      (fun j => randomFockDiskHole_tsum_lt_top j)
  exact ⟨randomFock ω, hentire, hnonpoly, hcofinite, hdense,
    fun z => norm_fockFunction_le_sqrt_two_mul_exp_sq
      (fun k => clipDisk (ω k)) (fun k => norm_clipDisk_le_one (ω k)) z⟩

/-- The final theorem with the growth bound and all project definitions expanded into the
quantifier order of the original statement. -/
theorem exists_transcendental_entire_with_explicit_derivative_zeros_and_growth :
    ∃ f : ℂ → ℂ,
      f ≠ 0 ∧
      AnalyticOnNhd ℂ f Set.univ ∧
      Differentiable ℂ f ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      (∀ z : ℂ, ‖f z‖ ≤ Real.sqrt 2 * Real.exp (‖z‖ ^ 2)) ∧
      (∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0) ∧
      (∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0}) := by
  obtain ⟨f, hentire, hnonpoly, hcofinite, hdense, hgrowth⟩ :=
    exists_transcendental_entire_with_cofinite_derivative_zeros_and_growth
  have hnonzero : f ≠ 0 := by
    intro hf
    apply hnonpoly
    refine ⟨0, fun z => ?_⟩
    rw [hf]
    simp
  have hquantifiers := (derivativesCofinitelyHit_iff f).mp hcofinite
  have hsubsequences : ∀ s : ℕ → ℕ, StrictMono s →
      Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0} := by
    intro s hs
    have hD : Dense (⋃ k, derivativeZeroSet f (s k)) := hdense s hs
    have heq : (⋃ k, derivativeZeroSet f (s k)) =
        {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0} := by
      ext z
      simp [derivativeZeroSet]
    rwa [heq] at hD
  have hdifferentiable : Differentiable ℂ f := by
    intro z
    exact (hentire z (Set.mem_univ z)).differentiableAt
  exact ⟨f, hnonzero, hentire, hdifferentiable,
    hnonpoly, hgrowth, hquantifiers, hsubsequences⟩

/-- Compatibility wrapper for the original fully expanded theorem statement. -/
theorem exists_transcendental_entire_with_explicit_derivative_zeros :
    ∃ f : ℂ → ℂ,
      f ≠ 0 ∧
      AnalyticOnNhd ℂ f Set.univ ∧
      Differentiable ℂ f ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      (∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0) ∧
      (∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0}) := by
  obtain ⟨f, hnonzero, hentire, hdifferentiable, hnonpoly, _hgrowth,
      hquantifiers, hsubsequences⟩ :=
    exists_transcendental_entire_with_explicit_derivative_zeros_and_growth
  exact ⟨f, hnonzero, hentire, hdifferentiable, hnonpoly, hquantifiers, hsubsequences⟩

end

end CofiniteDerivatives
end

open Set
open scoped Polynomial

namespace Submissions.Erdos906CofiniteDerivativeZeros.FullProof

/-- The full Erdős 906 theorem, ported from Eric Hou's complete Lean development. -/
theorem proof :
    ∃ f : ℂ → ℂ,
      f ≠ 0 ∧
      AnalyticOnNhd ℂ f Set.univ ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      ∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0} := by
  obtain ⟨f, hne, hentire, _hdifferentiable, hnonpoly, _hcofinite, hdense⟩ :=
    CofiniteDerivatives.exists_transcendental_entire_with_explicit_derivative_zeros
  exact ⟨f, hne, hentire, hnonpoly, hdense⟩

end Submissions.Erdos906CofiniteDerivativeZeros.FullProof
