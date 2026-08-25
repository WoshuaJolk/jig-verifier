import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Submissions.Erdos12TreePotentialThreshold.StrictVsKraft

private theorem geometric_carleson :
    ∀ (ρ : ℝ) (M : ℕ → ℝ),
      0 ≤ ρ →
      ρ < 1 →
      0 ≤ M 0 →
      (∀ n, M (n + 1) ≤ ρ * M n) →
      ∀ N, (∑ n ∈ Finset.range (N + 1), M n) ≤ M 0 / (1 - ρ) := by
  intro ρ M hρ hρ1 hM0 hcontract
  have hpoint : ∀ n, M n ≤ ρ ^ n * M 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          M (n + 1) ≤ ρ * M n := hcontract n
          _ ≤ ρ * (ρ ^ n * M 0) := mul_le_mul_of_nonneg_left ih hρ
          _ = ρ ^ (n + 1) * M 0 := by ring
  intro N
  calc
    (∑ n ∈ Finset.range (N + 1), M n) ≤
        ∑ n ∈ Finset.range (N + 1), ρ ^ n * M 0 := by
      exact Finset.sum_le_sum fun n _ => hpoint n
    _ = M 0 * ∑ n ∈ Finset.range (N + 1), ρ ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ M 0 * (1 - ρ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hM0
      have hsum :=
        (summable_geometric_of_lt_one hρ hρ1).sum_le_tsum
          (Finset.range (N + 1)) (fun n _ => pow_nonneg hρ n)
      rwa [tsum_geometric_of_lt_one hρ hρ1] at hsum
    _ = M 0 / (1 - ρ) := by rw [div_eq_mul_inv]

/-- Strict levelwise contraction gives a Carleson bound.  The boundary Kraft
condition does not: a full binary refinement tree has vanishing weight on
every branch but total weight one on every level. -/
theorem proof :
    (∀ (ρ : ℝ) (M : ℕ → ℝ),
      0 ≤ ρ →
      ρ < 1 →
      0 ≤ M 0 →
      (∀ n, M (n + 1) ≤ ρ * M n) →
      ∀ N, (∑ n ∈ Finset.range (N + 1), M n) ≤ M 0 / (1 - ρ)) ∧
    (∀ n : ℕ,
      2 * ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ) ^ n)⁻¹) ∧
    (∀ n : ℕ,
      (∑ _x : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹) = 1) ∧
    (∀ N : ℕ,
      ∑ n ∈ Finset.range (N + 1),
        (∑ _x : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹) = (N + 1 : ℕ)) ∧
    Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹)
      Filter.atTop (nhds 0) := by
  refine ⟨geometric_carleson, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [pow_succ]
    field_simp
  · intro n
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool]
    norm_num
  · intro N
    have hlevel : ∀ n : ℕ,
        (∑ _x : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹) = 1 := by
      intro n
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool]
      norm_num
    simp [hlevel]
  · have hpow :
        Filter.Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n))
          Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    convert hpow using 1
    ext n
    rw [one_div, inv_pow]

end Submissions.Erdos12TreePotentialThreshold.StrictVsKraft
