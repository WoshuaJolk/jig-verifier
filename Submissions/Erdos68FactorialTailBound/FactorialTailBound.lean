import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68FactorialTailBound.FactorialTailBound

private lemma denominator_lower (m k : ℕ) (hm : 2 ≤ m) :
    m * m.factorial * (m + 1) ^ k ≤
      (m + k + 1).factorial - 1 := by
  have hA0 : 0 < m.factorial * (m + 1) ^ k := by positivity
  have hA : 1 ≤ m.factorial * (m + 1) ^ k := by omega
  have hstep :
      m * m.factorial * (m + 1) ^ k + 1 ≤
        m.factorial * (m + 1) ^ (k + 1) := by
    calc
      m * m.factorial * (m + 1) ^ k + 1
          ≤ m * m.factorial * (m + 1) ^ k +
              m.factorial * (m + 1) ^ k :=
        Nat.add_le_add_left hA _
      _ = m.factorial * (m + 1) ^ (k + 1) := by
        rw [pow_succ]
        ring
  have hfac :
      m.factorial * (m + 1) ^ (k + 1) ≤
        (m + k + 1).factorial := by
    simpa [Nat.add_assoc] using
      (@Nat.factorial_mul_pow_le_factorial m (k + 1))
  omega

private lemma term_bound (m k : ℕ) (hm : 2 ≤ m) :
    (1 : ℝ) / (((m + k + 1).factorial - 1 : ℕ) : ℝ) ≤
      (1 / ((m : ℝ) * m.factorial)) *
        (1 / ((m : ℝ) + 1)) ^ k := by
  have hL : 0 < m * m.factorial * (m + 1) ^ k := by positivity
  have hle := denominator_lower m k hm
  have hleR :
      ((m * m.factorial * (m + 1) ^ k : ℕ) : ℝ) ≤
        (((m + k + 1).factorial - 1 : ℕ) : ℝ) := by
    exact_mod_cast hle
  calc
    (1 : ℝ) / (((m + k + 1).factorial - 1 : ℕ) : ℝ)
        ≤ 1 / ((m * m.factorial * (m + 1) ^ k : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast hL) hleR
    _ = (1 / ((m : ℝ) * m.factorial)) *
          (1 / ((m : ℝ) + 1)) ^ k := by
      push_cast
      rw [div_pow]
      field_simp
      simp

/-- The complete outer tail after row `m`, when scaled by `m!`, is at most
`(m+1)/m²`, hence strictly less than one. -/
theorem proof :
    ∀ m : ℕ, 2 ≤ m →
      let f : ℕ → ℝ := fun k =>
        1 / (((m + k + 1).factorial - 1 : ℕ) : ℝ)
      Summable f ∧
        0 ≤ (m.factorial : ℝ) * ∑' k, f k ∧
        (m.factorial : ℝ) * ∑' k, f k ≤
          (m + 1 : ℝ) / m ^ 2 ∧
        (m + 1 : ℝ) / m ^ 2 < 1 := by
  intro m hm
  dsimp
  let C : ℝ := 1 / ((m : ℝ) * m.factorial)
  let r : ℝ := 1 / ((m : ℝ) + 1)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    have h : (1 : ℝ) < (m : ℝ) + 1 := by
      exact_mod_cast (by omega : 1 < m + 1)
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) h
  have hg : Summable (fun k : ℕ => C * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hf :
      Summable (fun k : ℕ =>
        (1 : ℝ) / (((m + k + 1).factorial - 1 : ℕ) : ℝ)) := by
    exact Summable.of_nonneg_of_le
      (fun k => by positivity)
      (fun k => by simpa only [C, r] using term_bound m k hm)
      hg
  refine ⟨hf, ?_, ?_, ?_⟩
  · positivity
  · have hle := hf.tsum_le_tsum
        (fun k => by simpa only [C, r] using term_bound m k hm) hg
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
    dsimp [C, r] at hle
    have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hfacR : (0 : ℝ) < m.factorial := by positivity
    calc
      (m.factorial : ℝ) *
          ∑' k : ℕ, 1 / (↑((m + k + 1).factorial - 1) : ℝ)
          ≤ (m.factorial : ℝ) *
              ((1 / ((m : ℝ) * m.factorial)) *
                (1 - 1 / ((m : ℝ) + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (m + 1 : ℝ) / m ^ 2 := by
        field_simp [ne_of_gt hmR, ne_of_gt hfacR]
        ring
  · have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast
    rw [div_lt_one (by positivity : (0 : ℝ) < m ^ 2)]
    nlinarith

end Submissions.Erdos68FactorialTailBound.FactorialTailBound
