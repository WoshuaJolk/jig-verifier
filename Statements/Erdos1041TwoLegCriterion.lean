import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041TwoLegCriterion

open Polynomial MeasureTheory ENNReal

/-- One-dimensional Hausdorff measure, used as the geometric path length. -/
noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- Two-leg criterion for Erdős Problem 1041, in every degree: if two roots
`a`, `b` and a waypoint `w` satisfy `|a - w| + |w - b| < 2` and both straight
legs `a → w` and `w → b` stay inside the strict unit lemniscate, then the
conclusion of the problem holds for that polynomial. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
    f.rootSet ℂ ⊆ Metric.ball 0 1 →
    ∀ a b w : ℂ, ({a, b} : Multiset ℂ) ≤ f.roots →
    ‖a - w‖ + ‖w - b‖ < 2 →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (a + (t : ℂ) * (w - a))‖ < 1) →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f.eval (w + (t : ℂ) * (b - w))‖ < 1) →
      ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
        ∃ γ : Path z₁ z₂,
          Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
            pathLength (Set.range γ) < 2

theorem target : statement := sorry

end Statements.Erdos1041TwoLegCriterion
