import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041DegreeTwo

open Polynomial MeasureTheory ENNReal

/-- One-dimensional Hausdorff measure, used as the geometric path length. -/
noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- The degree-two case of Erdős Problem 1041: a monic complex quadratic whose
roots lie in the open unit disk has its two roots, counted with multiplicity,
joined inside its unit lemniscate by a path of length less than two. -/
abbrev statement : Prop :=
  ∀ (f : ℂ[X]), f.natDegree = 2 → f.Monic →
    f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
        ∃ γ : Path z₁ z₂,
          Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
            pathLength (Set.range γ) < 2

theorem target : statement := sorry

end Statements.Erdos1041DegreeTwo
