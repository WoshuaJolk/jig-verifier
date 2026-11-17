import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041ClosePair

open Polynomial MeasureTheory ENNReal

/-- One-dimensional Hausdorff measure, used as the geometric path length. -/
noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- Close-pair case of Erdős Problem 1041 in every degree `n`: if two roots
`a`, `b` (counted with multiplicity) satisfy `|a - b|² · 2^(n-2) < 4`, then the
conclusion of the problem holds. In degree three this is `|a - b| < √2`. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
    f.rootSet ℂ ⊆ Metric.ball 0 1 →
    ∀ a b : ℂ, ({a, b} : Multiset ℂ) ≤ f.roots →
    ‖a - b‖ ^ 2 * 2 ^ (n - 2) < 4 →
      ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
        ∃ γ : Path z₁ z₂,
          Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
            pathLength (Set.range γ) < 2

theorem target : statement := sorry

end Statements.Erdos1041ClosePair
