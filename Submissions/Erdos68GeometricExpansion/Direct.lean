import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Submissions.Erdos68GeometricExpansion.Direct

theorem proof :
    let f (n k : ℕ) : ℝ := 1 / ((n + 2).factorial : ℝ) ^ (k + 1)
    ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1) =
      ∑' n : ℕ, ∑' k : ℕ, f n k := by
  intro f
  apply tsum_congr
  intro n
  symm
  set r : ℝ := ((n + 2).factorial : ℝ)⁻¹ with hr_def
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_lt_one : r < 1 := inv_lt_one_of_one_lt₀ (by simp)
  have hgeom := hasSum_geometric_of_lt_one hr_nonneg hr_lt_one
  have hshift := hgeom.mul_left r
  have hf_eq : ∀ k, f n k = r * r ^ k := fun k => by
    simp only [f, hr_def]
    ring
  exact ((hshift.congr_fun hf_eq).tsum_eq.trans (by
    simp only [hr_def]
    field_simp))

end Submissions.Erdos68GeometricExpansion.Direct
