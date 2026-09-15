import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Submissions.J5P280DiscretePrefixEnergy.Proof

open Finset

noncomputable section

def cumulativeSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, f i

theorem prefix_succ (f : ℕ → ℝ) (n : ℕ) :
    cumulativeSum f (n+1) = cumulativeSum f n + f n := by
  exact sum_range_succ f n

theorem prefix_telescope (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range N, (cumulativeSum f (j+1))^2 / (((j:ℝ)+1)*((j:ℝ)+2))) =
      2 * (∑ j ∈ range N, f j * (cumulativeSum f (j+1) / ((j:ℝ)+1))) -
      (∑ j ∈ range N, (f j)^2 / ((j:ℝ)+1)) -
      (cumulativeSum f N)^2 / ((N:ℝ)+1) := by
  induction N with
  | zero => simp [cumulativeSum]
  | succ n ih =>
    simp only [sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [ih, prefix_succ]
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have h1 : (n:ℝ)+1 ≠ 0 := by linarith
    have h2 : (n:ℝ)+1+1 ≠ 0 := by linarith
    have h3 : (n:ℝ)+2 ≠ 0 := by linarith
    field_simp
    <;> ring

theorem weighted_square_comparison (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range N, (cumulativeSum f (j+1) / ((j:ℝ)+1))^2) ≤
      2 * (∑ j ∈ range N,
        (cumulativeSum f (j+1))^2 / (((j:ℝ)+1)*((j:ℝ)+2))) := by
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  have ha : 0 < (j:ℝ)+1 := by linarith
  have hb : 0 < (j:ℝ)+2 := by linarith
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos ha) (mul_pos ha hb)).2
  nlinarith [mul_nonneg (sq_nonneg (cumulativeSum f (j+1)))
    (mul_nonneg hj0 (le_of_lt ha))]

theorem discrete_hardy16 (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range N, (cumulativeSum f (j+1) / ((j:ℝ)+1))^2) ≤
      16 * (∑ j ∈ range N, (f j)^2) := by
  let R := ∑ j ∈ range N, (cumulativeSum f (j+1) / ((j:ℝ)+1))^2
  let T := ∑ j ∈ range N,
    (cumulativeSum f (j+1))^2 / (((j:ℝ)+1)*((j:ℝ)+2))
  let U := ∑ j ∈ range N, f j * (cumulativeSum f (j+1) / ((j:ℝ)+1))
  let E := ∑ j ∈ range N, (f j)^2
  have hR : R ≤ 2*T := weighted_square_comparison f N
  have hT0 : 0 ≤ T := by
    apply sum_nonneg
    intro j hj
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by positivity))
  have hE0 : 0 ≤ E := sum_nonneg (fun j hj => sq_nonneg _)
  have hD0 : 0 ≤ ∑ j ∈ range N, (f j)^2 / ((j:ℝ)+1) := by
    apply sum_nonneg
    intro j hj
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hLast : 0 ≤ (cumulativeSum f N)^2 / ((N:ℝ)+1) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have ht := prefix_telescope f N
  have hTU : T ≤ 2*U := by dsimp [T, U]; linarith
  have hU0 : 0 ≤ U := by linarith
  have hCS : U^2 ≤ E*R := sum_mul_sq_le_sq_mul_sq (range N) f
    (fun j => cumulativeSum f (j+1) / ((j:ℝ)+1))
  have hTCS : T^2 ≤ 4*E*R := by nlinarith
  have hET : E*R ≤ 2*E*T := by nlinarith [mul_nonneg hE0 (sub_nonneg.mpr hR)]
  have hsmall : T ≤ 8*E := by
    by_cases hz : T = 0
    · rw [hz]; linarith
    · have hp : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hz)
      nlinarith
  change R ≤ 16*E
  linarith

end


theorem solves :
  (∀ (f : ℕ → ℝ) (N : ℕ),
    (∑ j ∈ range N, (cumulativeSum f (j+1))^2 / (((j:ℝ)+1)*((j:ℝ)+2))) =
      2 * (∑ j ∈ range N, f j * (cumulativeSum f (j+1) / ((j:ℝ)+1))) -
      (∑ j ∈ range N, (f j)^2 / ((j:ℝ)+1)) -
      (cumulativeSum f N)^2 / ((N:ℝ)+1)) ∧
  (∀ (f : ℕ → ℝ) (N : ℕ),
    (∑ j ∈ range N, (cumulativeSum f (j+1) / ((j:ℝ)+1))^2) ≤
      16 * (∑ j ∈ range N, (f j)^2)) :=
  ⟨prefix_telescope, discrete_hardy16⟩

end Submissions.J5P280DiscretePrefixEnergy.Proof
