import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos68GeometricCarry.GeometricCarry

private lemma finite_geometric_remainder (B : ℝ) (hB0 : B ≠ 0)
    (hB1 : B ≠ 1) :
    ∀ J : ℕ,
      1 / (B - 1) - ∑ j ∈ Finset.range J, 1 / B ^ (j + 1) =
        1 / (B ^ J * (B - 1)) := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ih]
      field_simp
      ring

/-- After truncating the repeating base-`n!` expansion of `1 / (n! - 1)`
after `J` digits, the remainder is exactly known and lies strictly between one
and two units at the next base-`n!` position. -/
theorem proof :
    ∀ n J : ℕ, 3 ≤ n →
      let B : ℝ := n.factorial
      let R : ℝ :=
        1 / (B - 1) - ∑ j ∈ Finset.range J, 1 / B ^ (j + 1)
      R = 1 / (B ^ J * (B - 1)) ∧
        1 / B ^ (J + 1) < R ∧
        R < 2 / B ^ (J + 1) := by
  intro n J hn
  dsimp
  have hfacNat : 2 < n.factorial := by
    have hmono := Nat.factorial_le hn
    norm_num at hmono ⊢
    omega
  have hB : (2 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast hfacNat
  have hB0 : (n.factorial : ℝ) ≠ 0 := by positivity
  have hB1 : (n.factorial : ℝ) ≠ 1 := by linarith
  have hpow : 0 < (n.factorial : ℝ) ^ J := by positivity
  have hpow' : 0 < (n.factorial : ℝ) ^ (J + 1) := by positivity
  have hsub : 0 < (n.factorial : ℝ) - 1 := by linarith
  have heq := finite_geometric_remainder (n.factorial : ℝ) hB0 hB1 J
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    rw [div_lt_div_iff₀ hpow' (mul_pos hpow hsub)]
    rw [pow_succ]
    nlinarith
  · rw [heq]
    rw [div_lt_div_iff₀ (mul_pos hpow hsub) hpow']
    rw [pow_succ]
    nlinarith

end Submissions.Erdos68GeometricCarry.GeometricCarry
