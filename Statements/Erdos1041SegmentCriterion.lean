import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041SegmentCriterion

open Polynomial MeasureTheory ENNReal

/-- One-dimensional Hausdorff measure, used as the geometric path length. -/
noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- Segment criterion for Erdős Problem 1041, in every degree: if the straight
segment between two roots (counted with multiplicity) stays inside the strict
unit lemniscate, then the conclusion of the problem holds for that polynomial. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
    f.rootSet ℂ ⊆ Metric.ball 0 1 →
    ∀ a b : ℂ, ({a, b} : Multiset ℂ) ≤ f.roots →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (b - a))‖ < 1) →
      ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
        ∃ γ : Path z₁ z₂,
          Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
            pathLength (Set.range γ) < 2

theorem target : statement := sorry

end Statements.Erdos1041SegmentCriterion
