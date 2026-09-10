import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Lifts

/- Exact full-root reformulation. Neither side is asserted unconditionally. -/

open scoped Polynomial

namespace Submissions.Erdos1150IntegerCriterion.Main.Moments

noncomputable def circleSup (P : ℂ[X]) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖

noncomputable def energy (P : ℂ[X]) : ℝ :=
  ∑ i ∈ P.support, ‖P.coeff i‖ ^ 2

lemma energy_nonneg (P : ℂ[X]) : 0 ≤ energy P :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma circleSup_attained (P : ℂ[X]) :
    ∃ z ∈ Metric.sphere (0 : ℂ) 1, circleSup P = ‖P.eval z‖ := by
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn hne
    P.continuous.norm.continuousOn
  have hbdd : BddAbove (Set.range fun w : Metric.sphere (0 : ℂ) 1 =>
      ‖P.eval (w : ℂ)‖) := ⟨‖P.eval z‖, by rintro _ ⟨w, rfl⟩; exact hmax w.property⟩
  let : Nonempty (Metric.sphere (0 : ℂ) 1) := ⟨⟨z, hz⟩⟩
  exact ⟨z, hz, le_antisymm (ciSup_le fun w => hmax w.property)
    (le_ciSup_of_le hbdd ⟨z, hz⟩ le_rfl)⟩

lemma circleSup_nonneg (P : ℂ[X]) : 0 ≤ circleSup P := by
  obtain ⟨z, _, hz⟩ := circleSup_attained P
  rw [hz]
  exact norm_nonneg _

lemma norm_eval_le_circleSup (P : ℂ[X]) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) 1) : ‖P.eval z‖ ≤ circleSup P := by
  obtain ⟨M, hM⟩ :=
    (isCompact_sphere (0 : ℂ) 1).bddAbove_image P.continuous.norm.continuousOn
  have hbdd : BddAbove (Set.range fun v : Metric.sphere (0 : ℂ) 1 =>
      ‖P.eval (v : ℂ)‖) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact hM ⟨v, v.property, rfl⟩
  exact le_ciSup_of_le hbdd ⟨z, hz⟩ le_rfl

/-- Weighted Parseval: the same supremum controls every polynomial multiplier. -/
lemma weighted_energy (P Q : ℂ[X]) :
    energy (P * Q) ≤ circleSup P ^ 2 * energy Q := by
  have hPQ : CircleIntegrable (fun z => ‖(P * Q).eval z‖ ^ 2) 0 1 :=
    (((P * Q).continuous.norm).pow 2).continuousOn.circleIntegrable
    (show (0 : ℝ) ≤ 1 by norm_num)
  have hQ : CircleIntegrable (fun z => circleSup P ^ 2 * ‖Q.eval z‖ ^ 2) 0 1 :=
    ((continuous_const.mul ((Q.continuous.norm).pow 2))).continuousOn.circleIntegrable
    (show (0 : ℝ) ≤ 1 by norm_num)
  rw [energy, (P * Q).sum_sq_norm_coeff_eq_circleAverage]
  calc
    _ ≤ Real.circleAverage (fun z => circleSup P ^ 2 * ‖Q.eval z‖ ^ 2) 0 1 := by
      apply Real.circleAverage_mono hPQ hQ
      intro z hz
      simp only [abs_one] at hz
      simp only [Polynomial.eval_mul, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_eval_le_circleSup P hz) 2) (sq_nonneg _)
    _ = _ := by
      rw [show (fun z => circleSup P ^ 2 * ‖Q.eval z‖ ^ 2) =
        (fun z => circleSup P ^ 2 • ‖Q.eval z‖ ^ 2) by rfl,
        Real.circleAverage_fun_smul, ← Q.sum_sq_norm_coeff_eq_circleAverage]
      rfl

lemma energy_le_sup_sq (P : ℂ[X]) : energy P ≤ circleSup P ^ 2 := by
  have h1 : energy (1 : ℂ[X]) = 1 := by
    rw [energy, (1 : ℂ[X]).sum_sq_norm_coeff_eq_circleAverage]
    simp [Real.circleAverage_const]
  simpa only [mul_one, h1] using weighted_energy P 1

lemma circleSup_pow (P : ℂ[X]) (k : ℕ) : circleSup (P ^ k) = circleSup P ^ k := by
  obtain ⟨z, hz, heq⟩ := circleSup_attained (P ^ k)
  obtain ⟨w, hw, hweq⟩ := circleSup_attained P
  apply le_antisymm
  · rw [heq, Polynomial.eval_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_eval_le_circleSup P hz) k
  · rw [hweq, ← norm_pow, ← Polynomial.eval_pow]
    exact norm_eval_le_circleSup (P ^ k) hw

lemma sup_sq_le_card_energy (P : ℂ[X]) :
    circleSup P ^ 2 ≤ (P.support.card : ℝ) * energy P := by
  obtain ⟨z, hz, heq⟩ := circleSup_attained P
  have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
  have htri : ‖P.eval z‖ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ := by
    calc
      _ = ‖∑ i ∈ P.support, P.coeff i * z ^ i‖ := by
        rw [Polynomial.eval_eq_sum, Polynomial.sum]
      _ ≤ ∑ i ∈ P.support, ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_pow, hz1]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P.support
    (fun _ => (1 : ℝ)) (fun i => ‖P.coeff i‖)
  rw [heq]
  exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans (by simpa [energy] using hcs)

/-- All moments give certified lower and upper bounds for the exact circle supremum. -/
theorem moment_sandwich (P : ℂ[X]) (k : ℕ) :
    energy (P ^ k) ≤ circleSup P ^ (2 * k) ∧
    circleSup P ^ (2 * k) ≤ ((P ^ k).support.card : ℝ) * energy (P ^ k) := by
  constructor
  · simpa [circleSup_pow, ← pow_mul, Nat.mul_comm] using energy_le_sup_sq (P ^ k)
  · simpa [circleSup_pow, ← pow_mul, Nat.mul_comm] using sup_sq_le_card_energy (P ^ k)

theorem degree_moment_sandwich (P : ℂ[X]) (k : ℕ) :
    energy (P ^ k) ≤ circleSup P ^ (2 * k) ∧
    circleSup P ^ (2 * k) ≤ (k * P.natDegree + 1 : ℝ) * energy (P ^ k) := by
  have hcard : (P ^ k).support.card ≤ k * P.natDegree + 1 := by
    calc
      _ ≤ (Finset.range (k * P.natDegree + 1)).card := by
        apply Finset.card_le_card
        intro i hi
        apply Finset.mem_range.mpr
        have hdeg := Polynomial.le_natDegree_of_mem_supp i hi
        have hpow := Polynomial.natDegree_pow_le (p := P) (n := k)
        omega
      _ = _ := Finset.card_range _
  refine ⟨(moment_sandwich P k).1, (moment_sandwich P k).2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (energy_nonneg _)
  exact_mod_cast hcard

end Submissions.Erdos1150IntegerCriterion.Main.Moments

open Filter Topology

namespace Submissions.Erdos1150IntegerCriterion.Main.Forward

lemma eventually_sq_add_one_lt_pow {r : ℝ} (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 + 1 < r ^ n := by
  have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ 2 + 1) / r ^ n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa [add_div] using
      (tendsto_pow_const_div_const_pow_of_one_lt 2 hr).add
        (tendsto_pow_const_div_const_pow_of_one_lt 0 hr)
  have he : ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ 2 + 1) / r ^ n < 1 :=
    ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  exact he.mono fun n hn ↦ by
    simpa only [one_mul] using
      (div_lt_iff₀ (pow_pos (lt_trans zero_lt_one hr) n)).mp hn

lemma ratio_gt_one {c : ℝ} {q : ℕ} (hc : 0 < c) (hq : 1 / c < (q : ℝ)) :
    1 < ((q : ℝ) * (1 + c)) / ((q : ℝ) + 1) := by
  have hqc : 1 < (q : ℝ) * c := (div_lt_iff₀ hc).mp hq
  apply (one_lt_div (show (0 : ℝ) < (q : ℝ) + 1 by positivity)).mpr
  nlinarith only [hqc]

/-- Exponential growth absorbs the degree-dependent quadratic moment factor. -/
theorem eventually_forward_scale {c : ℝ} {q : ℕ}
    (hc : 0 < c) (hq : 1 / c < (q : ℝ)) :
    ∀ᶠ n : ℕ in atTop, q ≤ n ∧
      (n * n + 1 : ℝ) < (((q : ℝ) * (1 + c)) / ((q : ℝ) + 1)) ^ n := by
  exact (eventually_ge_atTop q).and (by
    simpa only [pow_two] using eventually_sq_add_one_lt_pow (ratio_gt_one hc hq))

/-- Generic numeric transfer from a strict supremum gap and the upper moment bound.
The scalar `S` may later be instantiated with coefficient energy. -/
theorem forward_energy_inequality {c M S : ℝ} {q n : ℕ}
    (hc : 0 < c) (hq : 1 / c < (q : ℝ)) (hn : q ≤ n)
    (hscale : (n : ℝ) ^ 2 + 1 <
      (((q : ℝ) * (1 + c)) / ((q : ℝ) + 1)) ^ n)
    (hroot : (1 + c) * Real.sqrt (n : ℝ) < M)
    (hupper : M ^ (2 * n) ≤ ((n : ℝ) ^ 2 + 1) * S) :
    ((q : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n < (q : ℝ) ^ n * S := by
  have ha : 0 < 1 + c := by linarith
  have hqc : 1 < (q : ℝ) * c := (div_lt_iff₀ hc).mp hq
  have hnc : 1 < (n : ℝ) * c := hqc.trans_le
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hc.le)
  have hM : 0 ≤ M :=
    (mul_nonneg ha.le (Real.sqrt_nonneg _)).trans hroot.le
  have hrootSq : (1 + c) ^ 2 * (n : ℝ) < M ^ 2 := by
    have hs := (sq_lt_sq₀ (mul_nonneg ha.le (Real.sqrt_nonneg _)) hM).mpr hroot
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using hs
  have hbase : (1 + c) * ((n : ℝ) + 1) < M ^ 2 := by
    have hboost := mul_pos ha (sub_pos.mpr hnc)
    nlinarith only [hrootSq, hboost]
  have hpower : ((1 + c) * ((n : ℝ) + 1)) ^ n ≤ M ^ (2 * n) := by
    simpa only [← pow_mul] using
      pow_le_pow_left₀ (mul_nonneg ha.le (by positivity)) hbase.le n
  have hden : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hratio :
      (((q : ℝ) * (1 + c)) / ((q : ℝ) + 1)) ^ n *
          (((q : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n) =
        (q : ℝ) ^ n * ((1 + c) * ((n : ℝ) + 1)) ^ n := by
    calc
      _ = ((((q : ℝ) * (1 + c)) / ((q : ℝ) + 1)) * ((q : ℝ) + 1)) ^ n *
          ((n : ℝ) + 1) ^ n := by rw [mul_pow]; ring
      _ = _ := by
        rw [div_mul_cancel₀ _ hden.ne']
        simp only [mul_pow]
        ring
  have hchain :
      ((n : ℝ) ^ 2 + 1) * (((q : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n) <
        ((n : ℝ) ^ 2 + 1) * ((q : ℝ) ^ n * S) := by
    calc
      _ < (((q : ℝ) * (1 + c)) / ((q : ℝ) + 1)) ^ n *
          (((q : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n) :=
        mul_lt_mul_of_pos_right hscale (mul_pos (pow_pos hden n) (pow_pos hN n))
      _ = (q : ℝ) ^ n * ((1 + c) * ((n : ℝ) + 1)) ^ n := hratio
      _ ≤ (q : ℝ) ^ n * M ^ (2 * n) :=
        mul_le_mul_of_nonneg_left hpower (pow_nonneg (Nat.cast_nonneg q) n)
      _ ≤ (q : ℝ) ^ n * (((n : ℝ) ^ 2 + 1) * S) :=
        mul_le_mul_of_nonneg_left hupper (pow_nonneg (Nat.cast_nonneg q) n)
      _ = _ := by ring
  exact (mul_lt_mul_iff_of_pos_left (show 0 < (n : ℝ) ^ 2 + 1 by positivity)).mp hchain

/-- Choose one positive integer denominator before the eventual degree and both scalars. -/
theorem eventually_forward_energy {c : ℝ} (hc : 0 < c) :
    ∃ q : ℕ, 0 < q ∧ ∀ᶠ n : ℕ in atTop, ∀ M S : ℝ,
      (1 + c) * Real.sqrt (n : ℝ) < M →
      M ^ (2 * n) ≤ ((n : ℝ) ^ 2 + 1) * S →
      ((q : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n < (q : ℝ) ^ n * S := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / c)
  refine ⟨q, ?_, ?_⟩
  · exact_mod_cast (lt_trans (one_div_pos.mpr hc) hq)
  · filter_upwards [eventually_forward_scale hc hq] with n hn
    intro M S hroot hupper
    exact forward_energy_inequality hc hq hn.1
      (by simpa only [pow_two] using hn.2) hroot hupper


end Submissions.Erdos1150IntegerCriterion.Main.Forward

open scoped Polynomial
open Filter Topology

namespace Submissions.Erdos1150IntegerCriterion.Main

open Submissions.Erdos1150IntegerCriterion.Main.Moments

-- Deliberately expanded: this is exactly Jig #249's original root type.
abbrev originalRoot : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
    ∀ P : ℂ[X],
      (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
      P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1,
          ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n

def integerEnergy (A : ℤ[X]) : ℤ :=
  ∑ i ∈ A.support, A.coeff i ^ 2

/-- One positive integer q, chosen before the eventual degree and sign polynomial.
Every quantity in the final strict inequality is an integer. -/
abbrev integerCriterion : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∀ᶠ n in Filter.atTop,
    ∀ A : ℤ[X],
      (∀ i ≤ A.natDegree, A.coeff i = -1 ∨ A.coeff i = 1) →
      A.natDegree = n →
        ((q : ℤ) + 1) ^ n * ((n : ℤ) + 1) ^ n <
          (q : ℤ) ^ n * integerEnergy (A ^ n)

/-- The exact root and the finite-integer reformulation. -/
abbrev desiredEquivalence : Prop := originalRoot ↔ integerCriterion

-- This shape check only unfolds the imported supremum definition.
example : originalRoot ↔
    (∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],
        (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
        P.natDegree = n →
          Submissions.Erdos1150IntegerCriterion.Main.Moments.circleSup P >
            (1 + c) * Real.sqrt n) := Iff.rfl

noncomputable def complexify (A : ℤ[X]) : ℂ[X] :=
  A.map (Int.castRingHom ℂ)

lemma complexify_natDegree (A : ℤ[X]) :
    (complexify A).natDegree = A.natDegree :=
  Polynomial.natDegree_map_eq_of_injective
    (Int.cast_injective (α := ℂ)) A

lemma complexify_coeff (A : ℤ[X]) (i : ℕ) :
    (complexify A).coeff i = (A.coeff i : ℂ) := by
  simp [complexify]

lemma complexify_pow (A : ℤ[X]) (n : ℕ) :
    complexify (A ^ n) = complexify A ^ n := by
  simp [complexify]

lemma complexify_energy (A : ℤ[X]) :
    Submissions.Erdos1150IntegerCriterion.Main.Moments.energy (complexify A) =
      (integerEnergy A : ℝ) := by
  unfold Submissions.Erdos1150IntegerCriterion.Main.Moments.energy integerEnergy complexify
  rw [Polynomial.support_map_of_injective A (Int.cast_injective (α := ℂ))]
  simp only [Polynomial.coeff_map, Int.coe_castRingHom, Complex.sq_norm,
    Complex.normSq_intCast, Int.cast_sum, Int.cast_pow]
  simp only [pow_two]

lemma exists_integer_littlewood (P : ℂ[X])
    (ha : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) :
    ∃ A : ℤ[X], complexify A = P ∧
      (∀ i ≤ A.natDegree, A.coeff i = -1 ∨ A.coeff i = 1) := by
  have hl : P ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
    apply (Polynomial.lifts_iff_coeff_lifts P).mpr
    intro i
    by_cases hi : i ≤ P.natDegree
    · rcases ha i hi with h | h
      · exact ⟨-1, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]
      simp
  obtain ⟨A, hA⟩ := (Polynomial.mem_lifts P).mp hl
  change complexify A = P at hA
  refine ⟨A, hA, ?_⟩
  intro i hi
  have hiP : i ≤ P.natDegree := by
    rw [← hA, complexify_natDegree]
    exact hi
  have hc := ha i hiP
  rw [← hA, complexify_coeff] at hc
  rcases hc with hc | hc
  · left
    exact Int.cast_injective (α := ℂ) (by simpa using hc)
  · right
    exact Int.cast_injective (α := ℂ) (by simpa using hc)

/-- The eventual integer criterion implies the original root. -/
theorem integerCriterion_implies_originalRoot (h : integerCriterion) : originalRoot := by
  obtain ⟨q, hq, he⟩ := h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let b : ℝ := ((q : ℝ) + 1) / (q : ℝ)
  have hb : 1 < b := by
    dsimp [b]
    apply (lt_div_iff₀ hqR).mpr
    linarith
  have hb0 : 0 ≤ b := by linarith
  have hsquare : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0
  have hsqrt : 1 < Real.sqrt b := by
    nlinarith [Real.sqrt_nonneg b]
  refine ⟨Real.sqrt b - 1, by linarith, ?_⟩
  filter_upwards [he] with n hn
  intro P ha hdeg
  obtain ⟨A, hA, haA⟩ := exists_integer_littlewood P ha
  have hAn : A.natDegree = n := by
    rw [← complexify_natDegree A, hA]
    exact hdeg
  have hInt := hn A haA hAn
  have hReal : ((q : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n <
      (q : ℝ) ^ n * (integerEnergy (A ^ n) : ℝ) := by
    exact_mod_cast hInt
  have henergy : (integerEnergy (A ^ n) : ℝ) = energy (P ^ n) := by
    rw [← complexify_energy, complexify_pow, hA]
  rw [henergy] at hReal
  have hp : (((q : ℝ) + 1) * ((n : ℝ) + 1)) ^ n <
      ((q : ℝ) * circleSup P ^ 2) ^ n := by
    calc
      _ = ((q : ℝ) + 1) ^ n * ((n : ℝ) + 1) ^ n := mul_pow _ _ _
      _ < (q : ℝ) ^ n * energy (P ^ n) := hReal
      _ ≤ (q : ℝ) ^ n * circleSup P ^ (2 * n) :=
        mul_le_mul_of_nonneg_left (moment_sandwich P n).1 (pow_nonneg hqR.le n)
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hbase : ((q : ℝ) + 1) * ((n : ℝ) + 1) <
      (q : ℝ) * circleSup P ^ 2 :=
    lt_of_pow_lt_pow_left₀ n (mul_nonneg hqR.le (sq_nonneg _)) hp
  have hqb : (q : ℝ) * b = (q : ℝ) + 1 := by
    dsimp [b]
    exact mul_div_cancel₀ _ hqR.ne'
  have hnorm : b * ((n : ℝ) + 1) < circleSup P ^ 2 := by
    apply (mul_lt_mul_iff_of_pos_left hqR).mp
    calc
      (q : ℝ) * (b * ((n : ℝ) + 1)) =
          ((q : ℝ) * b) * ((n : ℝ) + 1) := (mul_assoc _ _ _).symm
      _ = ((q : ℝ) + 1) * ((n : ℝ) + 1) := by rw [hqb]
      _ < (q : ℝ) * circleSup P ^ 2 := hbase
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hprod : (Real.sqrt b * Real.sqrt n) ^ 2 = b * n := by
    rw [mul_pow, hsquare, Real.sq_sqrt hn0]
  have hlt : Real.sqrt b * Real.sqrt n < circleSup P := by
    nlinarith [circleSup_nonneg P,
      mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg (n : ℝ))]
  change (1 + (Real.sqrt b - 1)) * Real.sqrt n < circleSup P
  convert hlt using 1; ring

-- A positive-degree threshold must remain eventual: it is false at degree zero.
example (q : ℕ) :
    ¬ (((q : ℤ) + 1) ^ 0 * ((0 : ℤ) + 1) ^ 0 <
      (q : ℤ) ^ 0 * integerEnergy ((1 : ℤ[X]) ^ 0)) := by
  have hs : (1 : ℤ[X]).support = {0} := by
    simpa only [Polynomial.C_1] using
      (Polynomial.support_C (show (1 : ℤ) ≠ 0 by decide))
  norm_num [integerEnergy, hs]

theorem originalRoot_implies_integerCriterion (h : originalRoot) : integerCriterion := by
  obtain ⟨c, hc, he⟩ := h
  obtain ⟨q, hq, hf⟩ := Forward.eventually_forward_energy hc
  refine ⟨q, hq, ?_⟩
  filter_upwards [he, hf] with n hroot hforward
  intro A ha hdeg
  have haC : ∀ i ≤ (complexify A).natDegree,
      (complexify A).coeff i = -1 ∨ (complexify A).coeff i = 1 := by
    intro i hi
    rw [complexify_natDegree] at hi
    rcases ha i hi with h | h <;> simp [complexify_coeff, h]
  have hdegC : (complexify A).natDegree = n := by
    rw [complexify_natDegree, hdeg]
  have hrootC : (1 + c) * Real.sqrt n < circleSup (complexify A) :=
    hroot (complexify A) haC hdegC
  have hupper : circleSup (complexify A) ^ (2 * n) ≤
      ((n : ℝ) ^ 2 + 1) * energy (complexify A ^ n) := by
    simpa only [hdegC, pow_two] using (degree_moment_sandwich (complexify A) n).2
  have hineq := hforward (circleSup (complexify A)) (energy (complexify A ^ n))
    hrootC hupper
  rw [← complexify_pow, complexify_energy] at hineq
  exact_mod_cast hineq

/-- Equivalence only: proving either side remains the full Littlewood problem. -/
theorem proof : desiredEquivalence :=
  ⟨originalRoot_implies_integerCriterion, integerCriterion_implies_originalRoot⟩

end Submissions.Erdos1150IntegerCriterion.Main
