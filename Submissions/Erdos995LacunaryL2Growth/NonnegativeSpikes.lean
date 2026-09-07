/-
Complete Jig265 counterexample, after Boon Suan Ho arXiv2604.18535v2.
Fresh Lean formalization of a nonnegative integer-base variant of the spike
construction. Exact cylinder measures, second-moment estimates, square-
integrability and the final canonical negation are all proved in this file.
No mathematical novelty is claimed.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated


namespace JigCampaign.Dyadic

open MeasureTheory Set
open scoped ENNReal

def hit (m : ℕ) (c : ℝ) : Set ℝ :=
  Ico 0 1 ∩ {x | Int.fract ((m : ℝ) * x) < c}

theorem hit_eq_intervals {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : c ≤ 1) :
    hit m c = ⋃ j ∈ Finset.range m, Ico ((j : ℝ) / m) ((j + c) / m) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  ext x
  constructor
  · rintro ⟨hx, hh⟩
    change Int.fract ((m : ℝ) * x) < c at hh
    have hy : 0 ≤ (m : ℝ) * x := mul_nonneg hmR.le hx.1
    let j : ℕ := ⌊(m : ℝ) * x⌋₊
    have hj : j < m := (Nat.floor_lt hy).mpr (by nlinarith [hx.2])
    have hlow : (j : ℝ) ≤ (m : ℝ) * x := Nat.floor_le hy
    have hfract : Int.fract ((m : ℝ) * x) = (m : ℝ) * x - j := by
      rw [Int.fract, natCast_floor_eq_intCast_floor hy]
    refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr hj, ?_⟩⟩
    constructor
    · apply (div_le_iff₀ hmR).mpr
      nlinarith
    · apply (lt_div_iff₀ hmR).mpr
      rw [hfract] at hh
      nlinarith
  · rintro hx
    obtain ⟨j, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hj, hx⟩ := mem_iUnion.mp hx
    have hjm : j < m := Finset.mem_range.mp hj
    have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast hjm
    have hlow : (j : ℝ) ≤ (m : ℝ) * x := by
      have := (div_le_iff₀ hmR).mp hx.1
      nlinarith
    have hupp : (m : ℝ) * x < j + c := by
      have := (lt_div_iff₀ hmR).mp hx.2
      nlinarith
    have hfloor : ⌊(m : ℝ) * x⌋ = (j : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by exact_mod_cast hlow, by
        push_cast
        linarith⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith
    · nlinarith
    · change Int.fract ((m : ℝ) * x) < c
      rw [Int.fract, hfloor]
      push_cast
      linarith

theorem grid_intervals_disjoint {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : c ≤ 1) :
    Pairwise (fun i j : ℕ => Disjoint (Ico ((i : ℝ) / m) ((i + c) / m))
      (Ico ((j : ℝ) / m) ((j + c) / m))) := by
  intro i j hij
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hli := (div_le_iff₀ hmR).mp hi.1
  have hui := (lt_div_iff₀ hmR).mp hi.2
  have hlj := (div_le_iff₀ hmR).mp hj.1
  have huj := (lt_div_iff₀ hmR).mp hj.2
  rcases lt_or_gt_of_ne hij with h | h
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    linarith
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    linarith

theorem volume_hit {m : ℕ} (hm : 0 < m) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    volume (hit m c) = ENNReal.ofReal c := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [hit_eq_intervals hm hc1]
  rw [measure_biUnion_finset (fun i _ j _ hij => grid_intervals_disjoint hm hc1 hij)
    (fun _ _ => measurableSet_Ico)]
  simp_rw [Real.volume_Ico, show ∀ j : ℕ, ((j : ℝ) + c) / m - j / m = c / m by
    intro j; ring]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  congr 1
  field_simp


theorem volume_grid_union {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : c ≤ 1)
    (S : Finset ℕ) :
    volume (⋃ j ∈ S, Ico ((j : ℝ) / m) ((j + c) / m)) =
      (S.card : ℝ≥0∞) * ENNReal.ofReal (c / m) := by
  rw [measure_biUnion_finset (fun i _ j _ hij => grid_intervals_disjoint hm hc hij)
    (fun _ _ => measurableSet_Ico)]
  simp_rw [Real.volume_Ico, show ∀ j : ℕ, ((j : ℝ) + c) / m - j / m = c / m by
    intro j; ring]
  simp


def pairIndices (A D B : ℕ) : Finset ℕ :=
  ((Finset.range A).product (Finset.range B)).image (fun jr => jr.1 * D + jr.2)

theorem pair_hit_eq_grid {A D B : ℕ} (hA : 0 < A) (hD : 0 < D)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hDc : (D : ℝ) * c = B) :
    hit A c ∩ hit (A * D) c =
      ⋃ t ∈ pairIndices A D B, Ico ((t : ℝ) / (A*D)) ((t+c)/(A*D)) := by
  have hAR : 0 < (A : ℝ) := by exact_mod_cast hA
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hMR : 0 < ((A * D : ℕ) : ℝ) := by positivity
  have hBD : B ≤ D := by exact_mod_cast (show (B : ℝ) ≤ D by nlinarith)
  ext x
  constructor
  · rintro ⟨hxA, hxM⟩
    rw [hit_eq_intervals hA hc1] at hxA
    rw [hit_eq_intervals (Nat.mul_pos hA hD) hc1] at hxM
    obtain ⟨j, hxA⟩ := mem_iUnion.mp hxA
    obtain ⟨hj, hxA⟩ := mem_iUnion.mp hxA
    obtain ⟨t, hxM⟩ := mem_iUnion.mp hxM
    obtain ⟨ht, hxM⟩ := mem_iUnion.mp hxM
    have hAl := (div_le_iff₀ hAR).mp hxA.1
    have hAu := (lt_div_iff₀ hAR).mp hxA.2
    have hMl := (div_le_iff₀ hMR).mp hxM.1
    have hMu := (lt_div_iff₀ hMR).mp hxM.2
    push_cast at hMl hMu
    have hjDt : j*D ≤ t := by
      have he : (j : ℝ) * D < (t : ℝ) + 1 := by nlinarith
      have hn : j*D < t+1 := by exact_mod_cast he
      omega
    have htB : t < j*D+B := by
      have he : (t : ℝ) < (j : ℝ) * D + B := by nlinarith
      exact_mod_cast he
    have hr : t-j*D < B := by omega
    have heq : j*D+(t-j*D)=t := by omega
    refine mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_image.mpr
      exact ⟨(j,t-j*D), Finset.mem_product.mpr ⟨hj, Finset.mem_range.mpr hr⟩, heq⟩
    · simpa only [Nat.cast_mul] using hxM
  · intro hx
    obtain ⟨t, hx⟩ := mem_iUnion.mp hx
    obtain ⟨ht, hx⟩ := mem_iUnion.mp hx
    obtain ⟨⟨j,r⟩, hjr, heq⟩ := Finset.mem_image.mp ht
    obtain ⟨hj,hr⟩ := Finset.mem_product.mp hjr
    dsimp at heq
    subst t
    have hjA : j < A := Finset.mem_range.mp hj
    have hrB : r < B := Finset.mem_range.mp hr
    have hrD : r < D := lt_of_lt_of_le hrB hBD
    have htM : j*D+r < A*D := by nlinarith
    have hMl := (div_le_iff₀ (show 0 < (A : ℝ)*D by positivity)).mp hx.1
    have hMu := (lt_div_iff₀ (show 0 < (A : ℝ)*D by positivity)).mp hx.2
    push_cast at hMl hMu
    constructor
    · rw [hit_eq_intervals hA hc1]
      refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, ?_⟩⟩
      constructor
      · apply (div_le_iff₀ hAR).mpr
        have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
        nlinarith
      · apply (lt_div_iff₀ hAR).mpr
        have hrR : (r : ℝ)+1 ≤ B := by exact_mod_cast hrB
        nlinarith
    · rw [hit_eq_intervals (Nat.mul_pos hA hD) hc1]
      refine mem_iUnion.mpr ⟨j*D+r, mem_iUnion.mpr ⟨Finset.mem_range.mpr htM, ?_⟩⟩
      simpa only [Nat.cast_mul] using hx


theorem pairIndices_card {A D B : ℕ} (hD : 0 < D) (hBD : B ≤ D) :
    (pairIndices A D B).card = A * B := by
  have hi : Set.InjOn (fun jr : ℕ × ℕ => jr.1 * D + jr.2)
      (↑((Finset.range A).product (Finset.range B)) : Set (ℕ × ℕ)) := by
    rintro ⟨j,r⟩ hjr ⟨j',r'⟩ hjr' he
    obtain ⟨_,hr⟩ := Finset.mem_product.mp hjr
    obtain ⟨_,hr'⟩ := Finset.mem_product.mp hjr'
    have hrD : r < D := lt_of_lt_of_le (Finset.mem_range.mp hr) hBD
    have hrD' : r' < D := lt_of_lt_of_le (Finset.mem_range.mp hr') hBD
    dsimp at he
    have hm := congrArg (fun n : ℕ => n % D) he
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt hrD, Nat.mod_eq_of_lt hrD'] at hm
    have hp : j*D=j'*D := by omega
    have hj : j=j' := Nat.eq_of_mul_eq_mul_right hD hp
    exact Prod.ext hj hm
  unfold pairIndices
  rw [Finset.card_image_iff.mpr hi, Finset.product_eq_sprod, Finset.card_product]
  simp

theorem volume_pair_hit {A D B : ℕ} (hA : 0 < A) (hD : 0 < D)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hDc : (D : ℝ) * c = B) :
    volume (hit A c ∩ hit (A*D) c) = ENNReal.ofReal (c^2) := by
  have hAR : 0 < (A : ℝ) := by exact_mod_cast hA
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hBD : B ≤ D := by exact_mod_cast (show (B : ℝ) ≤ D by nlinarith)
  rw [pair_hit_eq_grid hA hD hc0 hc1 hDc]
  simp only [← Nat.cast_mul]
  rw [volume_grid_union (Nat.mul_pos hA hD) hc1, pairIndices_card hD hBD]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (A*B))]
  congr 1
  push_cast
  rw [← hDc]
  field_simp


def periodicHit (m : ℕ) (c : ℝ) : Set ℝ :=
  {x | Int.fract ((m : ℝ) * x) < c}

lemma measurableSet_periodicHit (m : ℕ) (c : ℝ) : MeasurableSet (periodicHit m c) := by
  exact measurableSet_lt (measurable_fract.comp (measurable_const.mul measurable_id))
    measurable_const

lemma measurableSet_hit (m : ℕ) (c : ℝ) : MeasurableSet (hit m c) :=
  measurableSet_Ico.inter (measurableSet_periodicHit m c)

noncomputable def unitVolume : Measure ℝ := volume.restrict (Ico 0 1)

instance : IsFiniteMeasure unitVolume := by
  constructor
  simp [unitVolume]

lemma unitVolume_periodicHit {m : ℕ} (hm : 0 < m) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    unitVolume (periodicHit m c) = ENNReal.ofReal c := by
  rw [unitVolume, Measure.restrict_apply (measurableSet_periodicHit m c)]
  rw [Set.inter_comm]
  exact volume_hit hm hc0 hc1

lemma unitVolume_real_periodicHit {m : ℕ} (hm : 0 < m) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    unitVolume.real (periodicHit m c) = c := by
  rw [Measure.real, unitVolume_periodicHit hm hc0 hc1, ENNReal.toReal_ofReal hc0]

lemma unitVolume_pair_periodicHit {A D B : ℕ} (hA : 0 < A) (hD : 0 < D)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hDc : (D : ℝ) * c = B) :
    unitVolume (periodicHit A c ∩ periodicHit (A*D) c) = ENNReal.ofReal (c^2) := by
  rw [unitVolume, Measure.restrict_apply
    ((measurableSet_periodicHit A c).inter (measurableSet_periodicHit (A*D) c))]
  have he : (periodicHit A c ∩ periodicHit (A*D) c) ∩ Ico (0:ℝ) 1 =
      hit A c ∩ hit (A*D) c := by ext x; simp [hit, periodicHit]; tauto
  rw [he]
  exact volume_pair_hit hA hD hc0 hc1 hDc

lemma unitVolume_real_pair_periodicHit {A D B : ℕ} (hA : 0 < A) (hD : 0 < D)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hDc : (D : ℝ) * c = B) :
    unitVolume.real (periodicHit A c ∩ periodicHit (A*D) c) = c^2 := by
  rw [Measure.real, unitVolume_pair_periodicHit hA hD hc0 hc1 hDc,
    ENNReal.toReal_ofReal (sq_nonneg c)]


lemma unitVolume_real_power_pair {M Q i j : ℕ} (hM : 0 < M) (hQ : 2 ≤ Q)
    (hij : i ≠ j) :
    unitVolume.real (periodicHit (M*Q^i) (1/(Q:ℝ)) ∩
      periodicHit (M*Q^j) (1/(Q:ℝ))) = (1/(Q:ℝ))^2 := by
  have hQp : 0 < Q := by omega
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQp
  have hc0 : 0 < 1/(Q:ℝ) := by positivity
  have hc1 : 1/(Q:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hQR).mpr
    have : (1:ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    simpa using this
  have forward (a b : ℕ) (hab : a < b) :
      unitVolume.real (periodicHit (M*Q^a) (1/(Q:ℝ)) ∩
        periodicHit (M*Q^b) (1/(Q:ℝ))) = (1/(Q:ℝ))^2 := by
    have hd : 0 < b-a := Nat.sub_pos_of_lt hab
    have hscale : (M*Q^a) * Q^(b-a) = M*Q^b := by
      rw [Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hab.le]
    have hD : ((Q^(b-a) : ℕ) : ℝ) * (1/(Q:ℝ)) = (Q^(b-a-1) : ℕ) := by
      rw [show b-a=(b-a-1)+1 by omega, pow_succ]
      push_cast
      field_simp
    have hv := unitVolume_real_pair_periodicHit
      (Nat.mul_pos hM (pow_pos hQp a)) (pow_pos hQp (b-a)) hc0 hc1 hD
    simpa only [hscale] using hv
  rcases lt_or_gt_of_ne hij with h | h
  · exact forward i j h
  · rw [Set.inter_comm]
    exact forward j i h

end JigCampaign.Dyadic


namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open MeasureTheory Finset
open scoped ENNReal RealInnerProductSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma norm_toLp_sq_eq_integral_sq {F : X → ℝ} (hF : MemLp F 2 μ) :
    ‖hF.toLp F‖ ^ 2 = ∫ x, F x ^ 2 ∂μ := by
  calc
    ‖hF.toLp F‖ ^ 2 = inner ℝ (hF.toLp F) (hF.toLp F) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, ((hF.toLp F) x) ^ 2 ∂μ := by
      rw [L2.inner_def]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = ∫ x, F x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with x hx using congrArg (fun r : ℝ => r ^ 2) hx

noncomputable def hitIndicator (s : Set X) (x : X) : ℝ :=
  s.indicator (fun _ => (1 : ℝ)) x

lemma hitIndicator_mul (s t : Set X) (x : X) :
    hitIndicator s x * hitIndicator t x = hitIndicator (s ∩ t) x := by
  classical
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;>
    simp [hitIndicator, Set.indicator, hs, ht]

lemma integral_indicator_sum_sq {ι : Type*} [Fintype ι] [IsFiniteMeasure μ]
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i)) :
    (∫ x, (∑ i, hitIndicator (S i) x) ^ 2 ∂μ) =
      ∑ i, ∑ j, μ.real (S i ∩ S j) := by
  have hi (i j : ι) : Integrable (fun x => hitIndicator (S i ∩ S j) x) μ :=
    (integrable_const 1).indicator ((hS i).inter (hS j))
  have hfun (x : X) :
      (∑ i, hitIndicator (S i) x) ^ 2 =
        ∑ i, ∑ j, hitIndicator (S i ∩ S j) x := by
    simp_rw [sq, sum_mul, mul_sum, hitIndicator_mul]
  simp_rw [hfun]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  congr 1
  ext i
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  congr 1
  ext j
  exact integral_indicator_one ((hS i).inter (hS j))

lemma memLp_indicator_sum {ι : Type*} [Fintype ι] [IsFiniteMeasure μ]
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i)) :
    MemLp (fun x => ∑ i, hitIndicator (S i) x) 2 μ := by
  exact memLp_finsetSum _ fun i _ => (memLp_const 1).indicator (hS i)

lemma toLp_inner_eq_integral_mul {F G : X → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    inner ℝ (hF.toLp F) (hG.toLp G) = ∫ x, F x * G x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

lemma measure_nonzero_ge_half [IsFiniteMeasure μ] {F : X → ℝ}
    (hF : MemLp F 2 μ) (hm : Measurable F)
    (hmean : 1 ≤ ∫ x, F x ∂μ)
    (hsecond : (∫ x, F x ^ 2 ∂μ) ≤ 2 * (∫ x, F x ∂μ) ^ 2) :
    (1 / 2 : ℝ) ≤ μ.real {x | F x ≠ 0} := by
  let A : Set X := {x | F x ≠ 0}
  have hA : MeasurableSet A := by
    change MeasurableSet ((F ⁻¹' {(0 : ℝ)})ᶜ)
    exact (hm (measurableSet_singleton (0 : ℝ))).compl
  let I : X → ℝ := hitIndicator A
  have hI : MemLp I 2 μ := (memLp_const 1).indicator hA
  have hcross : (∫ x, F x * I x ∂μ) = ∫ x, F x ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : F x = 0 <;> simp [I, hitIndicator, A, Set.indicator, hx]
  have hIsq : (∫ x, I x ^ 2 ∂μ) = μ.real A := by
    calc
      (∫ x, I x ^ 2 ∂μ) = ∫ x, hitIndicator A x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ A <;> simp [I, hitIndicator, Set.indicator, hx]
      _ = μ.real A := integral_indicator_one hA
  have hc := real_inner_mul_inner_self_le (hF.toLp F) (hI.toLp I)
  rw [toLp_inner_eq_integral_mul hF hI, hcross,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    norm_toLp_sq_eq_integral_sq hF, norm_toLp_sq_eq_integral_sq hI, hIsq] at hc
  have hmeasure : 0 ≤ μ.real A := ENNReal.toReal_nonneg
  have hupper : (∫ x, F x ^ 2 ∂μ) * μ.real A ≤
      (2 * (∫ x, F x ∂μ) ^ 2) * μ.real A := mul_le_mul_of_nonneg_right hsecond hmeasure
  have hpos : 0 < (∫ x, F x ∂μ) ^ 2 := by positivity
  change (1 / 2 : ℝ) ≤ μ.real A
  nlinarith

lemma indicator_sum_moment_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsFiniteMeasure μ] (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    {p : ℝ} (hp : ∀ i, μ.real (S i) = p)
    (hpair : ∀ i j, i ≠ j → μ.real (S i ∩ S j) ≤ p ^ 2) :
    (∫ x, ∑ i, hitIndicator (S i) x ∂μ) = (Fintype.card ι : ℝ) * p ∧
      (∫ x, (∑ i, hitIndicator (S i) x) ^ 2 ∂μ) ≤
        (Fintype.card ι : ℝ) * p + ((Fintype.card ι : ℝ) * p) ^ 2 := by
  constructor
  · rw [integral_finsetSum _ (fun i _ => (integrable_const 1).indicator (hS i))]
    calc
      (∑ i, ∫ x, hitIndicator (S i) x ∂μ) = ∑ _i : ι, p := by
        apply sum_congr rfl
        intro i _
        exact (integral_indicator_one (hS i)).trans (hp i)
      _ = (Fintype.card ι : ℝ) * p := by simp
  · rw [integral_indicator_sum_sq S hS]
    calc
      (∑ i, ∑ j, μ.real (S i ∩ S j)) ≤
          ∑ i, ∑ j, ((if j = i then p else 0) + p ^ 2) := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        by_cases hij : j = i
        · subst j
          simp only [Set.inter_self, hp, ite_true]
          nlinarith [sq_nonneg p]
        · simpa only [hij, ite_false, zero_add] using hpair i j (Ne.symm hij)
      _ = (Fintype.card ι : ℝ) * p + ((Fintype.card ι : ℝ) * p) ^ 2 := by
        simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true,
          sum_const, card_univ, nsmul_eq_mul]
        ring

lemma finite_hits_positive_measure {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsFiniteMeasure μ] (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    {p : ℝ} (hp : ∀ i, μ.real (S i) = p)
    (hpair : ∀ i j, i ≠ j → μ.real (S i ∩ S j) ≤ p ^ 2)
    (hcount : 1 ≤ (Fintype.card ι : ℝ) * p) :
    (1 / 2 : ℝ) ≤ μ.real {x | (∑ i, hitIndicator (S i) x) ≠ 0} := by
  obtain ⟨hmean, hsecond⟩ := indicator_sum_moment_bounds S hS hp hpair
  apply measure_nonzero_ge_half (memLp_indicator_sum S hS)
  · exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hS i)
  · rwa [hmean]
  · rw [hmean]
    nlinarith

lemma exists_hit_of_sum_ne_zero {ι : Type*} [Fintype ι]
    (S : ι → Set X) (x : X) (h : (∑ i, hitIndicator (S i) x) ≠ 0) :
    ∃ i, x ∈ S i := by
  classical
  by_contra hn
  push_neg at hn
  have hz : ∀ i, hitIndicator (S i) x = 0 := fun i => by
    simp [hitIndicator, hn i]
  simp only [hz, sum_const_zero] at h
  exact h rfl

lemma scaled_indicator_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsFiniteMeasure μ] (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    {p H : ℝ} (hp : ∀ i, μ.real (S i) = p)
    (hpair : ∀ i j, i ≠ j → μ.real (S i ∩ S j) ≤ p ^ 2)
    (hF : MemLp (fun x => H * ∑ i, hitIndicator (S i) x) 2 μ) :
    ‖hF.toLp (fun x => H * ∑ i, hitIndicator (S i) x)‖ ^ 2 ≤
      H ^ 2 * ((Fintype.card ι : ℝ) * p + ((Fintype.card ι : ℝ) * p) ^ 2) := by
  rw [norm_toLp_sq_eq_integral_sq]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  simpa only [mul_pow] using
    mul_le_mul_of_nonneg_left (indicator_sum_moment_bounds S hS hp hpair).2 (sq_nonneg H)

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes


/- Internal complete-root development, adapted from Ho arXiv:2604.18535v2.
The nonnegative variant uses arbitrary integer bases and pair moments. -/
namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open Finset

noncomputable def dilate (m : ℕ) (x : ℝ) : ℝ := Int.fract (x * m)

lemma fract_fract_mul_nat (x : ℝ) (m : ℕ) :
    Int.fract (Int.fract x * m) = Int.fract (x * m) := by
  obtain ⟨z, hz⟩ := Int.fract_mul_natCast x m
  calc
    Int.fract (Int.fract x * m) = Int.fract (Int.fract (x * m)) :=
      Int.fract_eq_fract.mpr ⟨z, hz⟩
    _ = Int.fract (x * m) := Int.fract_fract _

lemma dilate_dilate (a b : ℕ) (x : ℝ) :
    dilate a (dilate b x) = dilate (a * b) x := by
  unfold dilate
  rw [fract_fract_mul_nat]
  congr 1
  push_cast
  ring

noncomputable def spike (height cutoff x : ℝ) : ℝ :=
  if x < cutoff then height else 0

noncomputable def block (height cutoff : ℝ) (layers base : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ range layers, spike height cutoff (dilate (base ^ q) x)

lemma spike_nonneg {height : ℝ} (hh : 0 ≤ height) (cutoff x : ℝ) :
    0 ≤ spike height cutoff x := by
  unfold spike
  split_ifs <;> positivity

lemma block_nonneg {height : ℝ} (hh : 0 ≤ height) (cutoff : ℝ)
    (layers base : ℕ) (x : ℝ) :
    0 ≤ block height cutoff layers base x := by
  exact sum_nonneg fun _ _ => spike_nonneg hh _ _

lemma block_at_dilate_ge_of_central_hit
    {height cutoff x : ℝ} {layers base length h r M : ℕ}
    (hh : 0 ≤ height) (hhL : h < layers) (hcentral : length ≤ h + 1)
    (hr : r < length) (hit : dilate (M * base ^ h) x < cutoff) :
    height ≤ block height cutoff layers base (dilate (M * base ^ r) x) := by
  have hrh : r ≤ h := by omega
  have hindex : h - r ∈ range layers := by simp only [mem_range]; omega
  have hprod : base ^ (h-r) * (M * base ^ r) = M * base ^ h := by
    calc
      base ^ (h-r) * (M * base ^ r) = M * (base ^ (h-r) * base ^ r) := by ring
      _ = M * base ^ ((h-r)+r) := by rw [pow_add]
      _ = M * base ^ h := by rw [Nat.sub_add_cancel hrh]
  have hterm : spike height cutoff
      (dilate (base ^ (h-r)) (dilate (M * base ^ r) x)) = height := by
    rw [dilate_dilate, hprod]
    exact if_pos hit
  calc
    height = spike height cutoff
        (dilate (base ^ (h-r)) (dilate (M * base ^ r) x)) := hterm.symm
    _ ≤ block height cutoff layers base (dilate (M * base ^ r) x) := by
      unfold block
      exact single_le_sum (f := fun q =>
        spike height cutoff (dilate (base ^ q) (dilate (M * base ^ r) x)))
        (fun _ _ => spike_nonneg hh _ _) hindex

lemma trial_amplification
    {height cutoff x : ℝ} {layers base length h M : ℕ}
    (hh : 0 ≤ height) (hhL : h < layers) (hcentral : length ≤ h + 1)
    (hit : dilate (M * base ^ h) x < cutoff) :
    (length : ℝ) * height ≤
      ∑ r ∈ range length,
        block height cutoff layers base (dilate (M * base ^ r) x) := by
  calc
    (length : ℝ) * height = ∑ _r ∈ range length, height := by simp
    _ ≤ _ := sum_le_sum fun r hr =>
      block_at_dilate_ge_of_central_hit hh hhL hcentral (mem_range.mp hr) hit

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes


namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes

namespace Parameters

def height (k : ℕ) : ℕ := 2 ^ (k+10)
def trialCount (k : ℕ) : ℕ := 2 ^ (6*k+21)
def cumulative : ℕ → ℕ
  | 0 => 0
  | k+1 => cumulative k + trialCount k

def layers (k : ℕ) : ℕ := 2 ^ (cumulative (k+1)+1)
def base (k : ℕ) : ℕ := layers k * height k ^ 2 * 16 ^ k

lemma trialCount_pos (k : ℕ) : 0 < trialCount k := by unfold trialCount; positivity
lemma trialCount_succ (k : ℕ) : trialCount (k+1) = 64 * trialCount k := by
  unfold trialCount
  rw [show 6*(k+1)+21 = (6*k+21)+6 by omega, pow_add]
  ring

lemma trialCount_eq (k : ℕ) : trialCount k = 2 * height k ^ 2 * 16 ^ k := by
  unfold trialCount height
  have hsquare : ((2 : ℕ) ^ (k+10)) ^ 2 = 2 ^ (2*k+20) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsixteen : (16 : ℕ) ^ k = 2 ^ (4*k) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
  rw [hsquare, hsixteen]
  calc
    (2 : ℕ) ^ (6*k+21) = 2 ^ ((2*k+20)+(4*k)+1) := by congr 1; omega
    _ = 2 * 2 ^ (2*k+20) * 2 ^ (4*k) := by
      rw [pow_add, pow_add]
      ring

lemma cumulative_strictMono : StrictMono cumulative := by
  apply strictMono_nat_of_lt_succ
  intro k
  change cumulative k < cumulative k + trialCount k
  have := trialCount_pos k
  omega

lemma cumulative_ge (k : ℕ) : k ≤ cumulative k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k hk =>
      change k+1 ≤ cumulative k + trialCount k
      have := trialCount_pos k
      omega

lemma cumulative_le_twice (k : ℕ) : cumulative (k+1) ≤ 2 * trialCount k := by
  induction k with
  | zero => simp [cumulative, trialCount]
  | succ k hk =>
      change cumulative (k+1) + trialCount (k+1) ≤ 2 * trialCount (k+1)
      rw [trialCount_succ]
      omega

lemma cumulative_bound (k : ℕ) : cumulative (k+1) ≤ 2 ^ (8*k+30) := by
  calc
    cumulative (k+1) ≤ 2 * trialCount k := cumulative_le_twice k
    _ = 2 ^ (6*k+22) := by
      unfold trialCount
      rw [show 6*k+22 = (6*k+21)+1 by omega, pow_succ]
      ring
    _ ≤ 2 ^ (8*k+30) := Nat.pow_le_pow_right (by decide) (by omega)

lemma layers_half (k : ℕ) : layers k / 2 = 2 ^ cumulative (k+1) := by
  unfold layers
  rw [pow_succ, Nat.mul_div_left]
  decide

lemma twice_layers_half (k : ℕ) : 2 * (layers k / 2) = layers k := by
  rw [layers_half]
  unfold layers
  rw [pow_succ]
  ring

lemma trial_length_le_half (k j : ℕ) (hj : j < cumulative (k+1)) :
    2 ^ j ≤ layers k / 2 := by
  rw [layers_half]
  exact Nat.pow_le_pow_right (by decide) hj.le

lemma hits_card (k : ℕ) : trialCount k * (layers k / 2) = base k := by
  rw [trialCount_eq]
  calc
    2 * height k ^ 2 * 16 ^ k * (layers k / 2) =
        (2 * (layers k / 2)) * height k ^ 2 * 16 ^ k := by ring
    _ = base k := by rw [twice_layers_half]; rfl

lemma stage_exists (j : ℕ) : ∃ k, j < cumulative (k+1) :=
  ⟨j, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (cumulative_ge (j+1))⟩

noncomputable def stage (j : ℕ) : ℕ := Nat.find (stage_exists j)

lemma stage_upper (j : ℕ) : j < cumulative (stage j+1) := Nat.find_spec (stage_exists j)

lemma stage_lower (j : ℕ) : cumulative (stage j) ≤ j := by
  by_cases h : stage j = 0
  · simp [h, cumulative]
  · have hp : 0 < stage j := Nat.pos_of_ne_zero h
    by_contra hh
    have hlt : j < cumulative (stage j) := by omega
    have hprev : j < cumulative ((stage j-1)+1) := by
      rw [Nat.sub_add_cancel hp]
      exact hlt
    have : stage j ≤ stage j-1 := Nat.find_min' (stage_exists j) hprev
    omega

lemma height_pos (k : ℕ) : 0 < height k := by unfold height; positivity
lemma layers_pos (k : ℕ) : 0 < layers k := by unfold layers; positivity
lemma base_ge_two (k : ℕ) : 2 ≤ base k := by
  have hL : 2 ≤ layers k := by
    unfold layers
    have hpow : (2 : ℕ)^1 ≤ 2^(cumulative (k+1)+1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    simpa using hpow
  have hH : 0 < height k ^ 2 := pow_pos (height_pos k) _
  have hA : 0 < 16 ^ k := by positivity
  unfold base
  exact hL.trans ((Nat.le_mul_of_pos_right (layers k) hH).trans
    (Nat.le_mul_of_pos_right (layers k * height k ^ 2) hA))

noncomputable def trialBase : ℕ → ℕ
  | 0 => 1
  | j+1 => trialBase j * base (stage j) ^ (layers (stage j) + 2 ^ j)

lemma trialBase_pos (j : ℕ) : 0 < trialBase j := by
  induction j with
  | zero => decide
  | succ j hj =>
      change 0 < trialBase j * base (stage j) ^ (layers (stage j) + 2 ^ j)
      exact Nat.mul_pos hj (pow_pos (by have := base_ge_two (stage j); omega) _)

lemma trialBase_dvd_succ (j : ℕ) : trialBase j ∣ trialBase (j+1) := by
  exact dvd_mul_right _ _

lemma trialBase_dvd_of_le {j l : ℕ} (hjl : j ≤ l) : trialBase j ∣ trialBase l := by
  induction hjl with
  | refl => exact dvd_refl _
  | step h ih => exact ih.trans (trialBase_dvd_succ _)

lemma trialBase_monotone : Monotone trialBase := by
  intro j l h
  exact Nat.le_of_dvd (trialBase_pos l) (trialBase_dvd_of_le h)

noncomputable def trialIndex (a : ℕ) : ℕ := Nat.log 2 (a+1)
noncomputable def offset (a : ℕ) : ℕ := a+1 - 2 ^ trialIndex a

lemma offset_lt (a : ℕ) : offset a < 2 ^ trialIndex a := by
  have hlo := Nat.pow_log_le_self 2 (show a+1 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (show 1 < 2 by decide) (a+1)
  rw [pow_succ] at hhi
  unfold offset trialIndex
  omega

lemma trialIndex_at (j r : ℕ) (hr : r < 2 ^ j) :
    trialIndex (2 ^ j - 1 + r) = j := by
  have hp : 0 < 2 ^ j := by positivity
  unfold trialIndex
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]
    omega

lemma offset_at (j r : ℕ) (hr : r < 2 ^ j) :
    offset (2 ^ j - 1 + r) = r := by
  unfold offset
  rw [trialIndex_at j r hr]
  have : 0 < 2 ^ j := by positivity
  omega

noncomputable def sequence (a : ℕ) : ℕ :=
  trialBase (trialIndex a) * base (stage (trialIndex a)) ^ offset a

lemma sequence_at (j r : ℕ) (hr : r < 2 ^ j) :
    sequence (2 ^ j - 1 + r) = trialBase j * base (stage j) ^ r := by
  unfold sequence
  rw [trialIndex_at j r hr, offset_at j r hr]

lemma sequence_pos (a : ℕ) : 0 < sequence a := by
  unfold sequence
  exact Nat.mul_pos (trialBase_pos _) (pow_pos (by have := base_ge_two (stage (trialIndex a)); omega) _)

lemma trialIndex_monotone : Monotone trialIndex := by
  intro a b hab
  exact Nat.log_mono_right (Nat.add_le_add_right hab 1)

lemma two_mul_pow_le_pow {Q p q : ℕ} (hQ : 2 ≤ Q) (hpq : p < q) :
    2 * Q ^ p ≤ Q ^ q := by
  calc
    2 * Q ^ p ≤ Q * Q ^ p := Nat.mul_le_mul_right _ hQ
    _ = Q ^ (p+1) := by rw [pow_succ]; ring
    _ ≤ Q ^ q := Nat.pow_le_pow_right (by omega) (by omega)

lemma sequence_twice_le_of_lt {a b : ℕ} (hab : a < b) :
    2 * sequence a ≤ sequence b := by
  have hlog : trialIndex a ≤ trialIndex b := trialIndex_monotone hab.le
  by_cases heq : trialIndex a = trialIndex b
  · have hlo_a := Nat.pow_log_le_self 2 (show a+1 ≠ 0 by omega)
    have hlo_b := Nat.pow_log_le_self 2 (show b+1 ≠ 0 by omega)
    have hoff : offset a < offset b := by
      change 2 ^ trialIndex a ≤ a+1 at hlo_a
      change 2 ^ trialIndex b ≤ b+1 at hlo_b
      unfold offset
      rw [heq] at hlo_a ⊢
      omega
    unfold sequence
    rw [heq]
    calc
      2 * (trialBase (trialIndex b) * base (stage (trialIndex b)) ^ offset a) =
          trialBase (trialIndex b) * (2 * base (stage (trialIndex b)) ^ offset a) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (two_mul_pow_le_pow (base_ge_two _) hoff)
  · have hjk : trialIndex a + 1 ≤ trialIndex b := by omega
    have hlen : offset a + 1 ≤ layers (stage (trialIndex a)) + 2 ^ trialIndex a := by
      have := offset_lt a
      omega
    calc
      2 * sequence a = trialBase (trialIndex a) *
          (2 * base (stage (trialIndex a)) ^ offset a) := by unfold sequence; ring
      _ ≤ trialBase (trialIndex a) *
          base (stage (trialIndex a)) ^ (layers (stage (trialIndex a)) + 2 ^ trialIndex a) :=
        Nat.mul_le_mul_left _ (two_mul_pow_le_pow (base_ge_two _) (by omega))
      _ = trialBase (trialIndex a + 1) := rfl
      _ ≤ trialBase (trialIndex b) := trialBase_monotone hjk
      _ ≤ sequence b := Nat.le_mul_of_pos_right _
        (pow_pos (by have := base_ge_two (stage (trialIndex b)); omega) _)

lemma sequence_lacunary (a : ℕ) : 2 * sequence a ≤ sequence (a+1) :=
  sequence_twice_le_of_lt (Nat.lt_succ_self a)

lemma stage_eq_of_bounds {j k : ℕ}
    (hl : cumulative k ≤ j) (hu : j < cumulative (k+1)) : stage j = k := by
  apply le_antisymm
  · exact Nat.find_min' (stage_exists j) hu
  · by_contra h
    have hsk : stage j + 1 ≤ k := by omega
    have hcum := cumulative_strictMono.monotone hsk
    have := stage_upper j
    omega

lemma stage_at_trial (k t : ℕ) (ht : t < trialCount k) :
    stage (cumulative k+t) = k := by
  apply stage_eq_of_bounds (by omega)
  change cumulative k+t < cumulative k+trialCount k
  omega

lemma base_mul_scale_dvd_later {j l h g : ℕ} (hjl : j < l)
    (hh : h < layers (stage j)) :
    base (stage j) * (trialBase j * base (stage j) ^ h) ∣
      trialBase l * base (stage l) ^ g := by
  have hpow : base (stage j) ^ (h+1) ∣
      base (stage j) ^ (layers (stage j) + 2 ^ j) :=
    pow_dvd_pow _ ((Nat.succ_le_iff.mpr hh).trans (Nat.le_add_right _ _))
  have hstep : base (stage j) * (trialBase j * base (stage j) ^ h) ∣ trialBase (j+1) := by
    change base (stage j) * (trialBase j * base (stage j) ^ h) ∣
      trialBase j * base (stage j) ^ (layers (stage j) + 2 ^ j)
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using mul_dvd_mul_left (trialBase j) hpow
  exact hstep.trans ((trialBase_dvd_of_le (by omega)).trans (dvd_mul_right _ _))

lemma base_mul_scale_dvd_same {M Q h g : ℕ} (hhg : h < g) :
    Q * (M * Q ^ h) ∣ M * Q ^ g := by
  have hpow : Q ^ (h+1) ∣ Q ^ g := pow_dvd_pow _ (by omega)
  simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using mul_dvd_mul_left M hpow

abbrev WindowIndex (k : ℕ) := Fin (trialCount k) × Fin (layers k / 2)

noncomputable def windowScale (k : ℕ) (u : WindowIndex k) : ℕ :=
  trialBase (cumulative k+u.1.val) * base k ^ (layers k/2+u.2.val)

lemma windowScale_pos (k : ℕ) (u : WindowIndex k) : 0 < windowScale k u := by
  unfold windowScale
  exact Nat.mul_pos (trialBase_pos _) (pow_pos (by have := base_ge_two k; omega) _)

lemma central_lt (k : ℕ) (q : Fin (layers k / 2)) : layers k/2+q.val < layers k := by
  have := q.isLt
  have := twice_layers_half k
  omega

lemma central_enough (k : ℕ) (t : Fin (trialCount k)) (q : Fin (layers k/2)) :
    2 ^ (cumulative k+t.val) ≤ (layers k/2+q.val)+1 := by
  have ht : cumulative k+t.val < cumulative (k+1) := by
    change cumulative k+t.val < cumulative k+trialCount k
    omega
  have := trial_length_le_half k (cumulative k+t.val) ht
  omega

lemma window_pair_divisibility (k : ℕ) (u v : WindowIndex k) (huv : u ≠ v) :
    base k * windowScale k u ∣ windowScale k v ∨
      base k * windowScale k v ∣ windowScale k u := by
  rcases lt_trichotomy u.1.val v.1.val with h | h | h
  · left
    have hs1 := stage_at_trial k u.1.val u.1.isLt
    have hs2 := stage_at_trial k v.1.val v.1.isLt
    have hd := base_mul_scale_dvd_later
      (j := cumulative k+u.1.val) (l := cumulative k+v.1.val)
      (h := layers k/2+u.2.val) (g := layers k/2+v.2.val)
      (by omega) (by rw [hs1]; exact central_lt k u.2)
    simpa only [hs1, hs2, windowScale] using hd
  · have huv1 : u.1 = v.1 := Fin.ext h
    have hne2 : u.2 ≠ v.2 := fun h2 => huv (Prod.ext huv1 h2)
    rcases lt_or_gt_of_ne (fun he => hne2 (Fin.ext he)) with hq | hq
    · left
      unfold windowScale
      rw [huv1]
      exact base_mul_scale_dvd_same (by omega)
    · right
      unfold windowScale
      rw [huv1]
      exact base_mul_scale_dvd_same (by omega)
  · right
    have hs1 := stage_at_trial k u.1.val u.1.isLt
    have hs2 := stage_at_trial k v.1.val v.1.isLt
    have hd := base_mul_scale_dvd_later
      (j := cumulative k+v.1.val) (l := cumulative k+u.1.val)
      (h := layers k/2+v.2.val) (g := layers k/2+u.2.val)
      (by omega) (by rw [hs2]; exact central_lt k v.2)
    simpa only [hs1, hs2, windowScale] using hd

lemma windowIndex_card (k : ℕ) : Fintype.card (WindowIndex k) = base k := by
  simpa only [WindowIndex, Fintype.card_prod, Fintype.card_fin] using hits_card k

end Parameters
end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes


namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open MeasureTheory Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma memLp_tsum_of_summable_norms (F : ℕ → X → ℝ)
    (hF : ∀ k, MemLp (F k) 2 μ)
    (hs : Summable fun k => ‖(hF k).toLp (F k)‖) :
    MemLp (fun x => ∑' k, F k x) 2 μ ∧
      ∀ᵐ x ∂μ, Summable (fun k => F k x) := by
  let g : ℕ → Lp ℝ 2 μ := fun k => (hF k).toLp (F k)
  have hn : (∑' k, ‖g k‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hs
  have hcoeff : ∀ᵐ x ∂μ, ∀ k, g k x = F k x :=
    ae_all_iff.mpr fun k => (hF k).coeFn_toLp
  have hsum := Lp.hasSum_coeFn_tsum hn
  have hpoint : ∀ᵐ x ∂μ, HasSum (fun k => F k x) ((∑' k, g k) x) := by
    filter_upwards [hsum, hcoeff] with x hx heq
    simpa only [heq] using hx
  constructor
  · apply (Lp.memLp (∑' k, g k)).ae_eq
    filter_upwards [hpoint] with x hx using hx.tsum_eq.symm
  · filter_upwards [hpoint] with x hx using hx.summable

lemma tsum_ge_term_of_nonnegative {F : ℕ → ℝ}
    (hF : ∀ k, 0 ≤ F k) (hs : Summable F) (k : ℕ) :
    F k ≤ ∑' i, F i := by
  exact hs.le_tsum k (fun _ _ => hF _)

lemma ae_tsum_ge_every_term (F : ℕ → X → ℝ)
    (hF : ∀ k, MemLp (F k) 2 μ)
    (hs : Summable fun k => ‖(hF k).toLp (F k)‖)
    (hnonneg : ∀ k x, 0 ≤ F k x) :
    ∀ᵐ x ∂μ, ∀ k, F k x ≤ ∑' i, F i x := by
  filter_upwards [(memLp_tsum_of_summable_norms F hF hs).2] with x hx
  exact fun k => tsum_ge_term_of_nonnegative (fun i => hnonneg i x) hx k

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes


set_option maxHeartbeats 2000000

namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes

lemma log_two_bounds : (1 / 2 : ℝ) < Real.log 2 ∧ Real.log 2 < 1 := by
  constructor
  · have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    norm_num at h
    linarith
  · have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h
    exact h

lemma log_pow_two_le (m : ℕ) : Real.log ((2 : ℝ) ^ m) ≤ m := by
  rw [Real.log_pow]
  calc
    (m : ℝ) * Real.log 2 ≤ (m : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left log_two_bounds.2.le (Nat.cast_nonneg m)
    _ = m := mul_one _

lemma height_sq_bound (k : ℕ) :
    8 * (k : ℝ) + 30 ≤ ((2 : ℝ) ^ (k + 8)) ^ 2 := by
  induction k with
  | zero => norm_num
  | succ k hk =>
      rw [show k + 1 + 8 = (k + 8) + 1 by omega, pow_succ (2 : ℝ) (k + 8)]
      push_cast
      nlinarith [sq_nonneg ((2 : ℝ) ^ (k + 8))]

lemma loglog_le_of_endpoint_bound {N R k : ℕ}
    (hN : 16 ≤ N) (hNR : N ≤ 2 ^ R) (hR : R ≤ 2 ^ (8 * k + 30)) :
    0 < Real.log (Real.log (N : ℝ)) ∧
      Real.log (Real.log (N : ℝ)) ≤ 8 * (k : ℝ) + 30 := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hRpos : (0 : ℝ) < R := by
    have : R ≠ 0 := by intro h; subst R; norm_num at hNR; omega
    exact_mod_cast Nat.pos_of_ne_zero this
  have hlogN_lower : 1 < Real.log (N : ℝ) := by
    have hmono := Real.log_le_log (x := (16 : ℝ)) (y := (N : ℝ))
      (by norm_num) (by exact_mod_cast hN)
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h16] at hmono
    linarith [log_two_bounds.1]
  refine ⟨Real.log_pos hlogN_lower, ?_⟩
  have hlogN_upper : Real.log (N : ℝ) ≤ R := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((2 : ℝ) ^ R) :=
        Real.log_le_log hNpos (by exact_mod_cast hNR)
      _ ≤ R := log_pow_two_le R
  calc
    Real.log (Real.log (N : ℝ)) ≤ Real.log (R : ℝ) :=
      Real.log_le_log (by linarith only [hlogN_lower]) hlogN_upper
    _ ≤ Real.log ((2 : ℝ) ^ (8 * k + 30)) :=
      Real.log_le_log hRpos (by exact_mod_cast hR)
    _ ≤ 8 * (k : ℝ) + 30 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using log_pow_two_le (8*k+30)

lemma normalization_large {N R k : ℕ} {total : ℝ}
    (hN : 16 ≤ N) (hNR : N ≤ 2 ^ R) (hR : R ≤ 2 ^ (8 * k + 30))
    (hsignal : (N : ℝ) * ((2 : ℝ) ^ (k + 10)) / 2 ≤ total) :
    2 ≤ total / ((N : ℝ) * Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
  obtain ⟨hp, hb⟩ := loglog_le_of_endpoint_bound hN hNR hR
  have hNpos : (0 : ℝ) < N := by positivity
  have hsqrtpos : 0 < Real.sqrt (Real.log (Real.log (N : ℝ))) := Real.sqrt_pos.mpr hp
  have hsqrt : Real.sqrt (Real.log (Real.log (N : ℝ))) ≤ (2 : ℝ) ^ (k + 8) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, hb.trans (height_sq_bound k)⟩
  apply (le_div_iff₀ (mul_pos hNpos hsqrtpos)).mpr
  have hh : (2 : ℝ) ^ (k + 10) = 4 * (2 : ℝ) ^ (k + 8) := by
    rw [show k + 10 = (k + 8) + 2 by omega, pow_add]
    ring
  rw [hh] at hsignal
  have hmul := mul_le_mul_of_nonneg_left hsqrt hNpos.le
  nlinarith only [hsignal, hmul]

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes


namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open MeasureTheory Filter Set
open scoped ENNReal Topology

lemma measure_frequent_ge {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (S : ℕ → Set X)
    (hm : ∀ k, MeasurableSet (S k)) {c : ℝ≥0∞}
    (hc : ∀ k, c ≤ μ (S k)) :
    c ≤ μ {x | ∃ᶠ k in atTop, x ∈ S k} := by
  let U : ℕ → Set X := fun N => ⋃ k ≥ N, S k
  have hmeas : ∀ N, MeasurableSet (U N) := fun _ =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hm k
  have hanti : Antitone U := by
    intro n m hnm x hx
    simp only [U, mem_iUnion] at hx ⊢
    obtain ⟨k, hmk, hk⟩ := hx
    exact ⟨k, hnm.trans hmk, hk⟩
  have hlower : ∀ N, c ≤ μ (U N) := by
    intro N
    exact (hc N).trans (measure_mono fun x hx => by
      simp only [U, mem_iUnion]
      exact ⟨N, le_rfl, hx⟩)
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hmeas n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ (U 0)⟩
  have hge : c ≤ μ (⋂ N, U N) := ge_of_tendsto ht (Eventually.of_forall hlower)
  have heq : (⋂ N, U N) = {x | ∃ᶠ k in atTop, x ∈ S k} := by
    ext x
    simp only [mem_iInter, U, mem_iUnion, mem_setOf_eq, frequently_atTop, exists_prop]
  rwa [heq] at hge

lemma not_ae_tendsto_zero_of_events {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (g : X → ℕ → ℝ) (S : ℕ → Set X)
    (hm : ∀ k, MeasurableSet (S k)) {c : ℝ≥0∞}
    (hcpos : 0 < c) (hc : ∀ k, c ≤ μ (S k))
    (hgood : ∀ᵐ x ∂μ, ∀ k, x ∈ S k → ∃ n ≥ k, 2 ≤ g x n) :
    ¬ ∀ᵐ x ∂μ, Tendsto (g x) atTop (nhds 0) := by
  intro hconv
  have hnot : ∀ᵐ x ∂μ, ¬ ∃ᶠ k in atTop, x ∈ S k := by
    filter_upwards [hconv, hgood] with x hx hgoodx
    intro hf
    have hevent : ∀ᶠ n in atTop, g x n < 1 :=
      (tendsto_order.mp hx).2 1 (by norm_num)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    obtain ⟨k, hNk, hSk⟩ := frequently_atTop.mp hf N
    obtain ⟨n, hkn, hgn⟩ := hgoodx k hSk
    have := hN n (hNk.trans hkn)
    linarith
  have hnull : μ {x | ∃ᶠ k in atTop, x ∈ S k} = 0 := by
    simpa only [not_not] using ae_iff.mp hnot
  have hbound := measure_frequent_ge S hm hc
  rw [hnull] at hbound
  exact (not_le_of_gt hcpos) hbound

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes

namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes

lemma pure_scale_bound {H L A : ℝ} (hH : 1 ≤ H) (hL : 0 < L) (hA : 1 ≤ A) :
    H ^ 2 * (L / (L * H ^ 2 * A) + (L / (L * H ^ 2 * A)) ^ 2) ≤ 4 / A := by
  have hHp : 0 < H := by linarith only [hH]
  have hAp : 0 < A := by linarith only [hA]
  have hHa : 1 ≤ H ^ 2 * A := by
    have hHs : 1 ≤ H ^ 2 := by nlinarith only [hH]
    exact le_trans (by simpa using hA) (mul_le_mul_of_nonneg_right hHs hAp.le)
  have he : L / (L * H ^ 2 * A) = 1 / (H ^ 2 * A) := by field_simp
  rw [he]
  let b : ℝ := 1 / (H ^ 2 * A)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa using hHa)
  have hb2 : b ^ 2 ≤ b := by nlinarith only [hb0, hb1]
  have hmul := mul_le_mul_of_nonneg_left hb2 (sq_nonneg H)
  have hcancel : H ^ 2 * b = 1 / A := by dsimp [b]; field_simp
  change H ^ 2 * (b + b ^ 2) ≤ 4 / A
  calc
    H ^ 2 * (b + b ^ 2) ≤ 2 * (H ^ 2 * b) := by nlinarith only [hmul]
    _ = 2 / A := by rw [hcancel]; ring
    _ ≤ 4 / A := div_le_div_of_nonneg_right (by norm_num) hAp.le

lemma parameter_norm_bound (k : ℕ) :
    (Parameters.height k : ℝ) ^ 2 *
      ((Parameters.layers k : ℝ) / Parameters.base k +
        ((Parameters.layers k : ℝ) / Parameters.base k) ^ 2) ≤
      (2 * (1/4 : ℝ) ^ k) ^ 2 := by
  have hH : 1 ≤ (Parameters.height k : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Parameters.height_pos k)
  have hL : 0 < (Parameters.layers k : ℝ) := by exact_mod_cast Parameters.layers_pos k
  have hA : (1 : ℝ) ≤ 16 ^ k := one_le_pow₀ (by norm_num)
  have hQ : (Parameters.base k : ℝ) =
      (Parameters.layers k : ℝ) * (Parameters.height k : ℝ) ^ 2 * (16 : ℝ) ^ k := by
    simp only [Parameters.base, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hQ]
  calc
    _ ≤ 4 / (16 : ℝ) ^ k := pure_scale_bound hH hL hA
    _ = (2 * (1/4 : ℝ) ^ k) ^ 2 := by
      have hp : ((1/4 : ℝ) ^ k) ^ 2 = (1/16 : ℝ) ^ k := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      rw [mul_pow, hp, div_pow, one_pow]
      norm_num [div_eq_mul_inv]

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes


namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open MeasureTheory Finset JigCampaign.Dyadic
open scoped ENNReal

lemma block_indicator_eq (H c : ℝ) (L Q M : ℕ) (x : ℝ) :
    block H c L Q (dilate M x) =
      H * ∑ i : Fin L, hitIndicator (periodicHit (M*Q^i.val) c) x := by
  unfold block
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [dilate_dilate]
  have he : dilate (Q^i.val*M) x = Int.fract ((M*Q^i.val : ℕ)*x) := by
    simp [dilate, Nat.mul_comm, mul_comm]
  rw [he]
  unfold spike hitIndicator periodicHit
  by_cases h : Int.fract ((M*Q^i.val : ℕ)*x) < c <;> simp [Set.indicator, h]

lemma block_shift_memLp (H c : ℝ) (L Q M : ℕ) :
    MemLp (fun x => block H c L Q (dilate M x)) 2 unitVolume := by
  have he : (fun x => block H c L Q (dilate M x)) =
      (fun x => H * ∑ i : Fin L, hitIndicator (periodicHit (M*Q^i.val) c) x) :=
    funext (block_indicator_eq H c L Q M)
  rw [he]
  exact (memLp_indicator_sum (fun i : Fin L => periodicHit (M*Q^i.val) c)
    (fun i => measurableSet_periodicHit _ _)).const_mul H

lemma block_shift_norm_sq_bound (H : ℝ) (L Q M : ℕ)
    (hQ : 2 ≤ Q) (hM : 0 < M) :
    ‖(block_shift_memLp H (1/(Q:ℝ)) L Q M).toLp
      (fun x => block H (1/(Q:ℝ)) L Q (dilate M x))‖ ^ 2 ≤
      H^2 * ((L:ℝ)/(Q:ℝ) + ((L:ℝ)/(Q:ℝ))^2) := by
  let S : Fin L → Set ℝ := fun i => periodicHit (M*Q^i.val) (1/(Q:ℝ))
  have hQp : 0 < Q := by omega
  have hQR : 0 < (Q:ℝ) := by exact_mod_cast hQp
  have hp (i : Fin L) : unitVolume.real (S i) = 1/(Q:ℝ) := by
    apply unitVolume_real_periodicHit (Nat.mul_pos hM (pow_pos hQp i.val))
    · positivity
    · apply (div_le_iff₀ hQR).mpr
      have : (1:ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      simpa using this
  have hpair (i j : Fin L) (hij : i ≠ j) :
      unitVolume.real (S i ∩ S j) ≤ (1/(Q:ℝ))^2 := by
    apply le_of_eq
    exact unitVolume_real_power_pair hM hQ (fun h => hij (Fin.ext h))
  have hF : MemLp (fun x => H * ∑ i : Fin L, hitIndicator (S i) x) 2 unitVolume :=
    (memLp_indicator_sum S (fun i => measurableSet_periodicHit _ _)).const_mul H
  have hb := scaled_indicator_sum_bound S (fun i => measurableSet_periodicHit _ _) hp hpair hF
  rw [norm_toLp_sq_eq_integral_sq] at hb ⊢
  simpa only [block_indicator_eq, S, Fintype.card_fin, mul_one_div] using hb


noncomputable def stageBlock (k : ℕ) : ℝ → ℝ :=
  block (Parameters.height k) (1/(Parameters.base k : ℝ))
    (Parameters.layers k) (Parameters.base k)

lemma stageBlock_shift_memLp (k M : ℕ) :
    MemLp (fun x => stageBlock k (dilate M x)) 2 unitVolume :=
  block_shift_memLp _ _ _ _ _

lemma stageBlock_shift_norm_bound (k M : ℕ) (hM : 0 < M) :
    ‖(stageBlock_shift_memLp k M).toLp (fun x => stageBlock k (dilate M x))‖ ≤
      2 * (1/4 : ℝ)^k := by
  have hb := block_shift_norm_sq_bound (Parameters.height k : ℝ)
    (Parameters.layers k) (Parameters.base k) M (Parameters.base_ge_two k) hM
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * (1/4:ℝ)^k)).mp
    (hb.trans (parameter_norm_bound k))

lemma stageBlock_shift_norms_summable (M : ℕ) (hM : 0 < M) :
    Summable (fun k => ‖(stageBlock_shift_memLp k M).toLp
      (fun x => stageBlock k (dilate M x))‖) := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (stageBlock_shift_norm_bound · M hM)
  exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)| < 1)).mul_left 2

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes

namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open MeasureTheory Finset
open scoped ENNReal
open Parameters JigCampaign.Dyadic

lemma unitVolume_real_divisible_pair {A B Q : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hQ : 2 ≤ Q) (hdvd : Q*A ∣ B) :
    unitVolume.real (periodicHit A (1/(Q:ℝ)) ∩ periodicHit B (1/(Q:ℝ))) =
      (1/(Q:ℝ)) ^ 2 := by
  have hQp : 0 < Q := by omega
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQp
  obtain ⟨d,hd⟩ := hdvd
  have hdp : 0 < d := by
    by_contra hn
    have : d = 0 := by omega
    rw [this, mul_zero] at hd
    omega
  have hscale : A*(Q*d) = B := by rw [hd]; ring
  have hc0 : 0 < 1/(Q:ℝ) := by positivity
  have hc1 : 1/(Q:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hQR).mpr
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    simpa using hQ1
  have hDc : ((Q*d : ℕ) : ℝ) * (1/(Q:ℝ)) = d := by
    push_cast
    field_simp
  have hv := unitVolume_real_pair_periodicHit hA (Nat.mul_pos hQp hdp) hc0 hc1 hDc
  simpa only [hscale] using hv

noncomputable def stageHitCount (k : ℕ) (x : ℝ) : ℝ :=
  ∑ u : WindowIndex k, hitIndicator
    (periodicHit (windowScale k u) (1/(base k : ℝ))) x

def stageSuccess (k : ℕ) : Set ℝ := {x | stageHitCount k x ≠ 0}

lemma measurable_stageHitCount (k : ℕ) : Measurable (stageHitCount k) := by
  apply Finset.measurable_sum
  intro u _
  exact measurable_const.indicator (measurableSet_periodicHit _ _)

lemma measurableSet_stageSuccess (k : ℕ) : MeasurableSet (stageSuccess k) := by
  change MeasurableSet (((stageHitCount k) ⁻¹' {(0 : ℝ)})ᶜ)
  exact ((measurable_stageHitCount k) (measurableSet_singleton _)).compl

lemma stageSuccess_real_measure (k : ℕ) : (1/2 : ℝ) ≤ unitVolume.real (stageSuccess k) := by
  let E : WindowIndex k → Set ℝ := fun u => periodicHit (windowScale k u) (1/(base k : ℝ))
  have hQ : 2 ≤ base k := base_ge_two k
  have hQR : 0 < (base k : ℝ) := by exact_mod_cast (show 0 < base k by omega)
  have hc0 : 0 ≤ 1/(base k : ℝ) := by positivity
  have hc1 : 1/(base k : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hQR).mpr
    have hQ1 : (1 : ℝ) ≤ base k := by exact_mod_cast (show 1 ≤ base k by omega)
    simpa using hQ1
  have hsingle : ∀ u, unitVolume.real (E u) = 1/(base k : ℝ) :=
    fun u => unitVolume_real_periodicHit (windowScale_pos k u) hc0 hc1
  have hpair : ∀ u v, u ≠ v → unitVolume.real (E u ∩ E v) ≤ (1/(base k : ℝ)) ^ 2 := by
    intro u v huv
    rcases window_pair_divisibility k u v huv with h | h
    · exact (unitVolume_real_divisible_pair (windowScale_pos k u) (windowScale_pos k v) hQ h).le
    · rw [Set.inter_comm]
      exact (unitVolume_real_divisible_pair (windowScale_pos k v) (windowScale_pos k u) hQ h).le
  have hcount : (Fintype.card (WindowIndex k) : ℝ) * (1/(base k : ℝ)) = 1 := by
    rw [windowIndex_card]
    field_simp
  exact finite_hits_positive_measure E (fun u => measurableSet_periodicHit _ _) hsingle hpair hcount.ge

lemma stageSuccess_measure (k : ℕ) : ENNReal.ofReal (1/2 : ℝ) ≤ unitVolume (stageSuccess k) := by
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top unitVolume (stageSuccess k))).mpr
    (stageSuccess_real_measure k)

lemma exists_hit_of_stageSuccess {k : ℕ} {x : ℝ} (hx : x ∈ stageSuccess k) :
    ∃ u : WindowIndex k, dilate (windowScale k u) x < 1/(base k : ℝ) := by
  obtain ⟨u,hu⟩ := exists_hit_of_sum_ne_zero
    (fun u : WindowIndex k => periodicHit (windowScale k u) (1/(base k : ℝ))) x hx
  refine ⟨u, ?_⟩
  simpa only [periodicHit, Set.mem_ofPred_eq, dilate, mul_comm] using hu

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes

namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open Finset
open Parameters

def endpoint (j : ℕ) : ℕ := 2 ^ (j+1)-1

lemma trial_sum_le_partial_sum (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (j : ℕ) :
    (∑ r ∈ range (2 ^ j), g (2 ^ j-1+r)) ≤ ∑ a ∈ range (endpoint j), g a := by
  let T := (range (2 ^ j)).image (fun r => 2 ^ j-1+r)
  have hT : T ⊆ range (endpoint j) := by
    intro a ha
    obtain ⟨r,hr,rfl⟩ := mem_image.mp ha
    have hr' := mem_range.mp hr
    have hp : 0 < 2 ^ j := by positivity
    simp only [mem_range, endpoint, pow_succ]
    omega
  have hs : (∑ a ∈ T, g a) = ∑ r ∈ range (2 ^ j), g (2 ^ j-1+r) := by
    apply sum_image
    intro a _ b _ h
    change 2 ^ j-1+a = 2 ^ j-1+b at h
    omega
  rw [← hs]
  exact sum_le_sum_of_subset_of_nonneg hT (fun a _ _ => hg a)

lemma endpoint_bounds (k : ℕ) (hk : 1 ≤ k) (u : WindowIndex k) :
    16 ≤ endpoint (cumulative k+u.1.val) ∧
    k ≤ endpoint (cumulative k+u.1.val) ∧
    endpoint (cumulative k+u.1.val) ≤ 2 ^ cumulative (k+1) := by
  let j := cumulative k+u.1.val
  have hjlow : cumulative k ≤ j := by dsimp [j]; omega
  have hjhigh : j < cumulative (k+1) := by
    change cumulative k+u.1.val < cumulative k+trialCount k
    exact Nat.add_lt_add_left u.1.isLt _
  have hjfour : 4 ≤ j := by
    have hfirst : 4 ≤ cumulative 1 := by norm_num [cumulative, trialCount]
    have hmono := cumulative_strictMono.monotone hk
    omega
  have hexp : 32 ≤ 2 ^ (j+1) := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 5 ≤ j+1 by omega)
    exact h
  have hge : k ≤ j := (cumulative_ge k).trans hjlow
  have hgexp := (j+1).lt_two_pow_self
  refine ⟨by change 16 ≤ 2 ^ (j+1)-1; omega, ?_, ?_⟩
  · change k ≤ 2 ^ (j+1)-1
    omega
  · exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

lemma stage_hit_gives_signal (k : ℕ) (u : WindowIndex k) (x : ℝ) (f : ℝ → ℝ)
    (hf : ∀ y, 0 ≤ f y)
    (hd : ∀ m : ℕ, 0 < m →
      block (height k : ℝ) (1/(base k : ℝ)) (layers k) (base k) (dilate m x) ≤
        f (dilate m x))
    (hhit : dilate (windowScale k u) x < 1/(base k : ℝ)) :
    (endpoint (cumulative k+u.1.val) : ℝ) * (height k : ℝ) / 2 ≤
      ∑ a ∈ range (endpoint (cumulative k+u.1.val)), f (dilate (sequence a) x) := by
  let j := cumulative k+u.1.val
  have hst : stage j = k := stage_at_trial k u.1.val u.1.isLt
  have hH : 0 ≤ (height k : ℝ) := Nat.cast_nonneg _
  have ht : (2 ^ j : ℕ) * (height k : ℝ) ≤
      ∑ r ∈ range (2 ^ j), block (height k : ℝ) (1/(base k : ℝ))
        (layers k) (base k) (dilate (trialBase j * base k ^ r) x) :=
    trial_amplification hH (central_lt k u.2) (central_enough k u.1 u.2) hhit
  have hdom : (∑ r ∈ range (2 ^ j), block (height k : ℝ) (1/(base k : ℝ))
      (layers k) (base k) (dilate (trialBase j * base k ^ r) x)) ≤
        ∑ r ∈ range (2 ^ j), f (dilate (trialBase j * base k ^ r) x) := by
    apply sum_le_sum
    intro r _
    exact hd _ (Nat.mul_pos (trialBase_pos _) (pow_pos (by have := base_ge_two k; omega) _))
  have hsum : (∑ r ∈ range (2 ^ j), f (dilate (trialBase j * base k ^ r) x)) =
      ∑ r ∈ range (2 ^ j), f (dilate (sequence (2 ^ j-1+r)) x) := by
    apply sum_congr rfl
    intro r hr
    rw [sequence_at j r (mem_range.mp hr), hst]
  have hpartial := trial_sum_le_partial_sum (fun a => f (dilate (sequence a) x))
    (fun a => hf _) j
  rw [← hsum] at hpartial
  have hN : endpoint j ≤ 2 * 2 ^ j := by unfold endpoint; rw [pow_succ]; omega
  have hNR : (endpoint j : ℝ) ≤ 2 * (2 ^ j : ℕ) := by exact_mod_cast hN
  have hs := ht.trans (hdom.trans hpartial)
  change (endpoint j : ℝ) * (height k : ℝ) / 2 ≤ _
  have hmul := mul_le_mul_of_nonneg_right hNR hH
  nlinarith only [hs, hmul]

lemma stage_hit_gives_large_normalization (k : ℕ) (hk : 1 ≤ k)
    (u : WindowIndex k) (x : ℝ) (f : ℝ → ℝ)
    (hf : ∀ y, 0 ≤ f y)
    (hd : ∀ m : ℕ, 0 < m →
      block (height k : ℝ) (1/(base k : ℝ)) (layers k) (base k) (dilate m x) ≤
        f (dilate m x))
    (hhit : dilate (windowScale k u) x < 1/(base k : ℝ)) :
    ∃ N ≥ k, 2 ≤ (∑ a ∈ range N, f (dilate (sequence a) x)) /
      ((N : ℝ) * Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
  obtain ⟨h16,hkN,hupper⟩ := endpoint_bounds k hk u
  refine ⟨endpoint (cumulative k+u.1.val), hkN, ?_⟩
  apply normalization_large h16 hupper (cumulative_bound k)
  simpa only [height, Nat.cast_pow, Nat.cast_ofNat] using stage_hit_gives_signal k u x f hf hd hhit

end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes


namespace Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
open MeasureTheory Filter
open scoped ENNReal Topology
open JigCampaign.Dyadic

noncomputable def counterF (x : ℝ) : ℝ := ∑' k, stageBlock k (dilate 1 x)

lemma counterF_nonneg (x : ℝ) : 0 ≤ counterF x := by
  apply tsum_nonneg
  intro k
  exact block_nonneg (Nat.cast_nonneg _) _ _ _ _

lemma counterF_memLp_unit : MemLp counterF 2 unitVolume := by
  exact (memLp_tsum_of_summable_norms
    (fun k x => stageBlock k (dilate 1 x)) (fun k => stageBlock_shift_memLp k 1)
    (stageBlock_shift_norms_summable 1 (by decide))).1

lemma counterF_memLp_closed :
    MemLp counterF 2 (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  simpa only [unitVolume, MeasureTheory.restrict_Ico_eq_restrict_Icc] using
    counterF_memLp_unit

lemma counterF_dilate (M : ℕ) (x : ℝ) :
    counterF (dilate M x) = ∑' k, stageBlock k (dilate M x) := by
  simp only [counterF, dilate_dilate, one_mul]

lemma counterF_dominates : ∀ᵐ x ∂unitVolume, ∀ M : ℕ, 0 < M →
    ∀ k : ℕ, stageBlock k (dilate M x) ≤ counterF (dilate M x) := by
  apply ae_all_iff.mpr
  intro M
  by_cases hM : 0 < M
  · have h := ae_tsum_ge_every_term
      (fun k x => stageBlock k (dilate M x))
      (fun k => stageBlock_shift_memLp k M)
      (stageBlock_shift_norms_summable M hM)
      (fun k x => block_nonneg (Nat.cast_nonneg _) _ _ _ _)
    filter_upwards [h] with x hx
    intro _ k
    rw [counterF_dilate]
    exact hx k
  · exact Eventually.of_forall (fun _ h => False.elim (hM h))

def IsLacunary (n : ℕ → ℕ) : Prop :=
  1 ≤ n 0 ∧ ∃ q : ℝ, 1 < q ∧ ∀ k : ℕ, q * n k ≤ n (k+1)

noncomputable def normalizedSum (n : ℕ → ℕ) (f : ℝ → ℝ)
    (α : ℝ) (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N, f (Int.fract (α * n k))) /
    ((N : ℝ) * Real.sqrt (Real.log (Real.log N)))

lemma sequence_isLacunary : IsLacunary Parameters.sequence := by
  refine ⟨Parameters.sequence_pos 0, 2, by norm_num, ?_⟩
  intro k
  exact_mod_cast Parameters.sequence_lacunary k

lemma counterexample_unit :
    ¬ ∀ᵐ α : ℝ ∂unitVolume,
      Tendsto (normalizedSum Parameters.sequence counterF α) atTop (nhds 0) := by
  apply not_ae_tendsto_zero_of_events
    (normalizedSum Parameters.sequence counterF) (fun k => stageSuccess (k+1))
    (fun k => measurableSet_stageSuccess (k+1))
    (by norm_num : 0 < ENNReal.ofReal (1/2:ℝ))
    (fun k => stageSuccess_measure (k+1))
  filter_upwards [counterF_dominates] with x hx
  intro k hk
  obtain ⟨u,hu⟩ := exists_hit_of_stageSuccess hk
  obtain ⟨N,hN,hlarge⟩ := stage_hit_gives_large_normalization (k+1) (by omega)
    u x counterF counterF_nonneg (fun M hM => hx M hM (k+1)) hu
  refine ⟨N, by omega, ?_⟩
  exact hlarge

/-- Complete Jig p265 root: the universal L2 lacunary estimate fails. -/
theorem proof :
  ¬ ∀ n : ℕ → ℕ, ∀ f : ℝ → ℝ,
    IsLacunary n →
    MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
    ∀ᵐ α : ℝ ∂volume,
      Tendsto (normalizedSum n f α) atTop (nhds 0) := by
  intro h
  have ha := h Parameters.sequence counterF sequence_isLacunary counterF_memLp_closed
  exact counterexample_unit (ae_restrict_of_ae ha)

#print axioms proof
end Submissions.Erdos995LacunaryL2Growth.NonnegativeSpikes
