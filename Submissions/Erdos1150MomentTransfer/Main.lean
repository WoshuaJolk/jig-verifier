import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped Polynomial

namespace Submissions.Erdos1150MomentTransfer.Main

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

lemma littlewood_energy (P : ℂ[X]) (n : ℕ)
    (ha : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1)
    (hn : P.natDegree = n) : energy P = (n : ℝ) + 1 := by
  classical
  have hnorm : ∀ i ≤ n, ‖P.coeff i‖ = 1 := by
    intro i hi
    rcases ha i (hn ▸ hi) with h | h <;> simp [h]
  have hs : P.support = Finset.range (n + 1) := by
    ext i
    simp only [Polynomial.mem_support_iff, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · intro hi
      by_contra h
      exact hi (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    · intro hi h
      have := hnorm i hi
      simp [h] at this
  unfold energy
  rw [hs]
  calc
    _ = ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hnorm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), one_pow]
    _ = _ := by simp

/-- A uniform fourth-moment excess suffices for the exact fixed-gap root.
The energy premise is explicit and is not established here. -/
theorem fourth_moment_suffices
    (henergy : ∃ δ > (0 : ℝ), ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],
        (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
        P.natDegree = n →
        (1 + δ) * ((n : ℝ) + 1) ^ 2 ≤ energy (P ^ 2)) :
    ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],
        (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
        P.natDegree = n →
        circleSup P > (1 + c) * Real.sqrt n := by
  obtain ⟨δ, hδ, henergy⟩ := henergy
  have hbase : 0 ≤ 1 + δ := by linarith
  have hsq : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt hbase
  have hspos : 1 < Real.sqrt (1 + δ) := by
    nlinarith [Real.sqrt_nonneg (1 + δ)]
  refine ⟨Real.sqrt (1 + δ) - 1, by linarith, ?_⟩
  filter_upwards [henergy] with n he
  intro P ha hn
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hu := weighted_energy P P
  rw [← pow_two, littlewood_energy P n ha hn] at hu
  have hl := (he P ha hn).trans hu
  have hb : (1 + δ) * ((n : ℝ) + 1) ≤ circleSup P ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    nlinarith [hl]
  have hrad := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hprod : (Real.sqrt (1 + δ) * Real.sqrt n) ^ 2 = (1 + δ) * n := by
    rw [mul_pow, hsq, hrad]
  have hlt : Real.sqrt (1 + δ) * Real.sqrt n < circleSup P := by
    nlinarith [circleSup_nonneg P,
      mul_nonneg (Real.sqrt_nonneg (1 + δ)) (Real.sqrt_nonneg (n : ℝ))]
  convert hlt using 1; ring

theorem proof :
    (∀ P Q : ℂ[X], energy (P * Q) ≤ circleSup P ^ 2 * energy Q) ∧
    (∀ (P : ℂ[X]) (k : ℕ),
      energy (P ^ k) ≤ circleSup P ^ (2 * k) ∧
      circleSup P ^ (2 * k) ≤ (k * P.natDegree + 1 : ℝ) * energy (P ^ k)) ∧
    ((∃ δ > (0 : ℝ), ∀ᶠ n in Filter.atTop,
        ∀ P : ℂ[X],
          (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
          P.natDegree = n →
          (1 + δ) * ((n : ℝ) + 1) ^ 2 ≤ energy (P ^ 2)) →
      ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
        ∀ P : ℂ[X],
          (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
          P.natDegree = n →
          circleSup P > (1 + c) * Real.sqrt n) :=
  ⟨weighted_energy, degree_moment_sandwich, fourth_moment_suffices⟩

end Submissions.Erdos1150MomentTransfer.Main
