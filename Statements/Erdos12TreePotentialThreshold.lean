import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# The strict-contraction threshold for refinement-tree potentials

A strict contraction of total mass between levels gives a geometric Carleson
bound.  Mere Kraft conservation together with decay along every branch does
not: branching entropy can exactly cancel the branchwise decay.
-/

namespace Statements.Erdos12TreePotentialThreshold

abbrev statement : Prop :=
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
    Filter.atTop (nhds 0)

theorem target : statement := sorry

end Statements.Erdos12TreePotentialThreshold
