import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Submissions.Erdos967ZetaSeriesRefutation.Control

open scoped BigOperators
open scoped Classical

theorem proof (h : False) :
    ¬ (∀ (S : Set ℕ), (∀ n ∈ S, 1 < n) →
      Summable (fun n => if n ∈ S then (n : ℝ)⁻¹ else 0) →
      ∀ (t : ℝ),
        1 + (∑' n, if n ∈ S then
          (n : ℂ) ^ (-(1 + Complex.I * t)) else 0) ≠ 0) :=
  h.elim

end Submissions.Erdos967ZetaSeriesRefutation.Control
