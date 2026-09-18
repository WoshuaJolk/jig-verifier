import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
A limitation of scalar reflection inequalities, not a model of self-avoiding
walks and not a refutation of Jig #289. There are b+2 equally weighted labels:
one has distance 2R+2 and the remaining b+1 labels have distance b.
-/

namespace PlanarSAWCountingBarrier

def twoLevelDistance (b R : ℕ) (i : Fin (b + 2)) : ℕ :=
  if i = 0 then 2 * R + 2 else b

/-- Every cutoff pair in the stated range obeys the stronger reflected-tail
inequality, including the cutoff m=b where its multiplicity is tight. -/
theorem all_cutoff_counts (b R m r : ℕ) (hmr : m ≤ r) (hrR : r ≤ R) :
    (Finset.univ.filter (fun i : Fin (b + 2) => twoLevelDistance b R i ≤ m)).card ≤
      (m + 1) * (Finset.univ.filter (fun i : Fin (b + 2) =>
        2 * (r + 1) - m ≤ twoLevelDistance b R i)).card := by
  by_cases hmb : m < b
  · have hempty : (Finset.univ.filter
        (fun i : Fin (b + 2) => twoLevelDistance b R i ≤ m)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hd := (Finset.mem_filter.mp hi).2
      by_cases hi0 : i = 0
      · simp only [twoLevelDistance, if_pos hi0] at hd
        omega
      · simp only [twoLevelDistance, if_neg hi0] at hd
        omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · have hbm : b ≤ m := by omega
    have hsub : (Finset.univ.filter
        (fun i : Fin (b + 2) => twoLevelDistance b R i ≤ m)) ⊆
        (Finset.univ.erase (0 : Fin (b + 2))) := by
      intro i hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
      intro hi0
      have hd := (Finset.mem_filter.mp hi).2
      simp only [twoLevelDistance, if_pos hi0] at hd
      omega
    have hlow : (Finset.univ.filter
        (fun i : Fin (b + 2) => twoLevelDistance b R i ≤ m)).card ≤ b + 1 := by
      have h := Finset.card_le_card hsub
      simpa using h
    have hhigh : 1 ≤ (Finset.univ.filter (fun i : Fin (b + 2) =>
        2 * (r + 1) - m ≤ twoLevelDistance b R i)).card := by
      apply Finset.one_le_card.mpr
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ 0, ?_⟩⟩
      simp [twoLevelDistance]
      omega
    calc
      _ ≤ b + 1 := hlow
      _ ≤ m + 1 := by omega
      _ = (m + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left (m + 1) hhigh

theorem packed_cutoff_iff (R r : ℕ) :
    (2 * r + 1) ^ 2 < (2 * R + 1) ^ 2 + 1 ↔ r ≤ R := by
  constructor
  · intro h
    by_contra hn
    have hlt : 2 * R + 1 < 2 * r + 1 := by omega
    have hp := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)
    omega
  · intro h
    have hle : 2 * r + 1 ≤ 2 * R + 1 := by omega
    have hp := Nat.pow_le_pow_left hle 2
    omega

theorem cutoff_b_saturated (b R r : ℕ) (hbr : b ≤ r) (hrR : r ≤ R) :
    (Finset.univ.filter (fun i : Fin (b + 2) => twoLevelDistance b R i ≤ b)).card =
      (b + 1) * (Finset.univ.filter (fun i : Fin (b + 2) =>
        2 * (r + 1) - b ≤ twoLevelDistance b R i)).card := by
  have hlow (i : Fin (b + 2)) : twoLevelDistance b R i ≤ b ↔ i ≠ 0 := by
    by_cases hi : i = 0
    · simp [twoLevelDistance, hi]
      omega
    · simp [twoLevelDistance, hi]
  have hhigh (i : Fin (b + 2)) :
      2 * (r + 1) - b ≤ twoLevelDistance b R i ↔ i = 0 := by
    by_cases hi : i = 0
    · simp [twoLevelDistance, hi]
      omega
    · simp [twoLevelDistance, hi]
      omega
  simp_rw [hlow, hhigh]
  simp [Finset.filter_ne', Finset.filter_eq']

def modelLength (b : ℕ) : ℕ := (2 * b ^ 2 + 1) ^ 2

abbrev modelDistance (b : ℕ) := twoLevelDistance b (b ^ 2)

theorem all_admissible_counts (b m r : ℕ) (hmr : m ≤ r)
    (hpacked : (2 * r + 1) ^ 2 < modelLength b + 1) :
    (Finset.univ.filter (fun i : Fin (b + 2) => modelDistance b i ≤ m)).card ≤
      (m + 1) * (Finset.univ.filter (fun i : Fin (b + 2) =>
        2 * (r + 1) - m ≤ modelDistance b i)).card :=
  all_cutoff_counts b (b ^ 2) m r hmr ((packed_cutoff_iff (b ^ 2) r).mp hpacked)

theorem twoLevelDistance_le_length (b R : ℕ) (hbR : b ≤ R) (hR : 1 ≤ R)
    (i : Fin (b + 2)) : twoLevelDistance b R i ≤ (2 * R + 1) ^ 2 := by
  by_cases hi : i = 0
  · simp only [twoLevelDistance, if_pos hi]
    nlinarith [Nat.zero_le (R ^ 2)]
  · simp only [twoLevelDistance, if_neg hi]
    nlinarith [Nat.zero_le (R ^ 2)]

theorem modelDistance_support (b : ℕ) (hb : 2 ≤ b) (i : Fin (b + 2)) :
    1 ≤ modelDistance b i ∧ modelDistance b i ≤ modelLength b := by
  have hbR : b ≤ b ^ 2 := by simpa only [pow_two] using Nat.le_mul_self b
  have hR : 1 ≤ b ^ 2 := by omega
  refine ⟨?_, twoLevelDistance_le_length b (b ^ 2) hbR hR i⟩
  by_cases hi : i = 0
  · simp only [modelDistance, twoLevelDistance, if_pos hi]
    omega
  · simp only [modelDistance, twoLevelDistance, if_neg hi]
    omega

theorem twoLevelDistance_sum (b R : ℕ) :
    (∑ i : Fin (b + 2), (twoLevelDistance b R i : ℝ)) =
      ((b : ℝ) + 1) * b + 2 * R + 2 := by
  rw [Fin.sum_univ_succ]
  simp [twoLevelDistance]
  ring

noncomputable def modelMean (b : ℕ) : ℝ :=
  (∑ i : Fin (b + 2), (modelDistance b i : ℝ)) / ((b : ℝ) + 2)

theorem modelMean_formula (b : ℕ) :
    modelMean b = (3 * (b : ℝ) ^ 2 + b + 2) / ((b : ℝ) + 2) := by
  unfold modelMean modelDistance
  rw [twoLevelDistance_sum]
  push_cast
  congr 1
  ring

theorem modelMean_nonneg (b : ℕ) : 0 ≤ modelMean b := by
  unfold modelMean
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  · have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith

theorem modelMean_le_three_mul (b : ℕ) (hb : 2 ≤ b) : modelMean b ≤ 3 * (b : ℝ) := by
  have hb' : (2 : ℝ) ≤ b := Nat.cast_le.mpr hb
  rw [modelMean_formula]
  apply (div_le_iff₀ (by linarith : 0 < (b : ℝ) + 2)).mpr
  nlinarith

theorem modelMean_ge_self (b : ℕ) (hb : 2 ≤ b) : (b : ℝ) ≤ modelMean b := by
  have hb' : (2 : ℝ) ≤ b := Nat.cast_le.mpr hb
  rw [modelMean_formula]
  apply (le_div_iff₀ (by linarith : 0 < (b : ℝ) + 2)).mpr
  nlinarith [sq_nonneg ((b : ℝ) - 1)]

theorem modelLength_sqrt (b : ℕ) :
    Real.sqrt (modelLength b : ℝ) = 2 * (b : ℝ) ^ 2 + 1 := by
  have h : (modelLength b : ℝ) = (2 * (b : ℝ) ^ 2 + 1) ^ 2 := by
    simp [modelLength]
  rw [h, Real.sqrt_sq_eq_abs]
  apply abs_of_nonneg
  nlinarith [sq_nonneg (b : ℝ)]

theorem modelMean_quarterroot_bounds (b : ℕ) (hb : 2 ≤ b) :
    Real.sqrt (Real.sqrt (modelLength b : ℝ)) / 2 ≤ modelMean b ∧
      modelMean b ≤ 3 * Real.sqrt (Real.sqrt (modelLength b : ℝ)) := by
  have hb' : (2 : ℝ) ≤ b := Nat.cast_le.mpr hb
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hinner : 0 ≤ 2 * (b : ℝ) ^ 2 + 1 := by nlinarith [sq_nonneg (b : ℝ)]
  have hrootlo : (b : ℝ) ≤ Real.sqrt (2 * (b : ℝ) ^ 2 + 1) := by
    apply (Real.le_sqrt hb0 hinner).mpr
    nlinarith [sq_nonneg (b : ℝ)]
  have hroothi : Real.sqrt (2 * (b : ℝ) ^ 2 + 1) ≤ 2 * (b : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hmeanlo := modelMean_ge_self b hb
  have hmeanhi := modelMean_le_three_mul b hb
  rw [modelLength_sqrt]
  constructor <;> linarith

theorem modelMean_ratio_le (b : ℕ) (hb : 2 ≤ b) :
    modelMean b / Real.sqrt (modelLength b : ℝ) ≤ 3 / (2 * (b : ℝ)) := by
  have hb' : (2 : ℝ) ≤ b := Nat.cast_le.mpr hb
  have hden : 0 < 2 * (b : ℝ) ^ 2 + 1 := by nlinarith [sq_nonneg (b : ℝ)]
  rw [modelLength_sqrt]
  calc
    modelMean b / (2 * (b : ℝ) ^ 2 + 1) ≤
        (3 * (b : ℝ)) / (2 * (b : ℝ) ^ 2 + 1) :=
      div_le_div_of_nonneg_right (modelMean_le_three_mul b hb) (le_of_lt hden)
    _ ≤ 3 / (2 * (b : ℝ)) := by
      apply (div_le_div_iff₀ hden (by linarith : 0 < 2 * (b : ℝ))).mpr
      nlinarith

/-- Even all admissible scalar reflection inequalities together with positive
distances bounded by the path length permit a subdiffusive first moment. -/
theorem modelMean_ratio_tendsto_zero :
    Filter.Tendsto (fun b : ℕ => modelMean b / Real.sqrt (modelLength b : ℝ))
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun b : ℕ => (b : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Filter.Tendsto (fun b : ℕ => 3 / (2 * (b : ℝ)))
      Filter.atTop (nhds 0) := by
    have h := hinv.const_mul (3 / 2 : ℝ)
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_zero, zero_mul,
      mul_assoc, mul_left_comm, mul_comm]
      using h
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun b =>
      div_nonneg (modelMean_nonneg b) (Real.sqrt_nonneg _))
  · exact Filter.eventually_atTop.mpr ⟨2, fun b hb => modelMean_ratio_le b hb⟩
  · exact hupper

end PlanarSAWCountingBarrier

namespace Submissions.J5P289ScalarReflectionBarrier.Proof

open PlanarSAWCountingBarrier

abbrev statement : Prop :=
  (∀ b m r : ℕ, m ≤ r → (2 * r + 1) ^ 2 < modelLength b + 1 →
    (Finset.univ.filter (fun i : Fin (b + 2) => modelDistance b i ≤ m)).card ≤
      (m + 1) * (Finset.univ.filter (fun i : Fin (b + 2) =>
        2 * (r + 1) - m ≤ modelDistance b i)).card) ∧
  (∀ b : ℕ, 2 ≤ b → ∀ i : Fin (b + 2),
    1 ≤ modelDistance b i ∧ modelDistance b i ≤ modelLength b) ∧
  (∀ b : ℕ,
    modelMean b = (3 * (b : ℝ) ^ 2 + b + 2) / ((b : ℝ) + 2)) ∧
  (∀ b : ℕ, 2 ≤ b →
    Real.sqrt (Real.sqrt (modelLength b : ℝ)) / 2 ≤ modelMean b ∧
      modelMean b ≤ 3 * Real.sqrt (Real.sqrt (modelLength b : ℝ))) ∧
  Filter.Tendsto (fun b : ℕ => modelMean b / Real.sqrt (modelLength b : ℝ))
    Filter.atTop (nhds 0)

/-- Exact conjunction of the preserved independently proved scalar-model facts. -/
theorem proof : statement :=
  ⟨PlanarSAWCountingBarrier.all_admissible_counts,
   PlanarSAWCountingBarrier.modelDistance_support,
   PlanarSAWCountingBarrier.modelMean_formula,
   PlanarSAWCountingBarrier.modelMean_quarterroot_bounds,
   PlanarSAWCountingBarrier.modelMean_ratio_tendsto_zero⟩

end Submissions.J5P289ScalarReflectionBarrier.Proof
