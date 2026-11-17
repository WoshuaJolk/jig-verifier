import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041SegmentFailsCubic

open Polynomial

/-- The straight-segment method for Erdős Problem 1041 is dead in degree three:
some monic cubic with all roots in the open unit disk has the property that the
straight segment between any two distinct roots leaves the strict unit
lemniscate. -/
abbrev statement : Prop :=
  ∃ f : ℂ[X], f.natDegree = 3 ∧ f.Monic ∧ f.rootSet ℂ ⊆ Metric.ball 0 1 ∧
    ∀ a b : ℂ, a ∈ f.roots → b ∈ f.roots → a ≠ b →
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 1 ≤ ‖f.eval (a + (t : ℂ) * (b - a))‖

theorem target : statement := sorry

end Statements.Erdos1041SegmentFailsCubic
