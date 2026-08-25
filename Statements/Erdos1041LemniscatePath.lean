import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Statements.Erdos1041LemniscatePath

open Polynomial MeasureTheory ENNReal

/-- One-dimensional Hausdorff measure, used as the geometric path length in
the Erdős--Herzog--Piranian formulation. -/
noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- Erdős Problem 1041: a monic polynomial of degree at least two whose roots
lie in the open unit disk has two roots, counted with multiplicity, joined
inside its unit lemniscate by a path of length less than two. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
    f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
        ∃ γ : Path z₁ z₂,
          Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
            pathLength (Set.range γ) < 2

theorem target : statement := sorry

end Statements.Erdos1041LemniscatePath
