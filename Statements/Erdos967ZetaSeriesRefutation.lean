import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Statements.Erdos967ZetaSeriesRefutation

open scoped BigOperators
open scoped Classical

/-- Erdős Problem 967 has a negative answer: there is a set of integers above one
with summable reciprocals for which the associated Dirichlet series vanishes at
some point on the line `re = 1`. -/
abbrev statement : Prop :=
  ¬ (∀ (S : Set ℕ), (∀ n ∈ S, 1 < n) →
    Summable (fun n => if n ∈ S then (n : ℝ)⁻¹ else 0) →
    ∀ (t : ℝ),
      1 + (∑' n, if n ∈ S then
        (n : ℂ) ^ (-(1 + Complex.I * t)) else 0) ≠ 0)

theorem target : statement := by
  sorry

end Statements.Erdos967ZetaSeriesRefutation
