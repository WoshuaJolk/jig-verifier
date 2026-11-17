import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041PureBinomial

open Polynomial MeasureTheory ENNReal

/-- One-dimensional Hausdorff measure, used as the geometric path length. -/
noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- Erdős Problem 1041 for the binomials `z ^ n - c` with `|c| < 1`, in every
degree `n ≥ 2`: the polynomial satisfies the hypotheses of the problem and two
of its roots are joined inside the lemniscate by a path of length below two. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ c : ℂ, ‖c‖ < 1 →
    (X ^ n - C c : ℂ[X]).natDegree = n ∧ (X ^ n - C c : ℂ[X]).Monic ∧
    (X ^ n - C c : ℂ[X]).rootSet ℂ ⊆ Metric.ball 0 1 ∧
      ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ (X ^ n - C c : ℂ[X]).roots ∧
        ∃ γ : Path z₁ z₂,
          Set.range γ ⊆ {z : ℂ | ‖(X ^ n - C c : ℂ[X]).eval z‖ < 1} ∧
            pathLength (Set.range γ) < 2

theorem target : statement := sorry

end Statements.Erdos1041PureBinomial
