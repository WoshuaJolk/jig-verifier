import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041SharpTwo

open Polynomial MeasureTheory ENNReal

/-- One-dimensional Hausdorff measure, used as the geometric path length. -/
noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- The constant 2 in Erdős Problem 1041 cannot be lowered: for every `ε > 0`
some monic quadratic with both roots in the open unit disk has the property
that every path joining two of its roots (counted with multiplicity), inside
the lemniscate or not, has length at least `2 - ε`. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : ℂ[X], f.natDegree = 2 ∧ f.Monic ∧
    f.rootSet ℂ ⊆ Metric.ball 0 1 ∧
    ∀ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots →
      ∀ γ : Path z₁ z₂, ENNReal.ofReal (2 - ε) ≤ pathLength (Set.range γ)

theorem target : statement := sorry

end Statements.Erdos1041SharpTwo
