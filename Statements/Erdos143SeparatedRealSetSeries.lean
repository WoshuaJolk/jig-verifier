import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.Erdos143SeparatedRealSetSeries

/-- A countably infinite subset of `(1, ∞)` satisfying Erdős's
multiplicative separation condition. -/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  A ⊆ Set.Ioi (1 : ℝ) ∧ Set.Infinite A ∧ Set.Countable A ∧
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|

/-- Erdős Problem 143, the still-open weighted-series part. -/
abbrev statement : Prop :=
  ∀ A : Set ℝ, WellSeparatedSet A →
    Summable fun x : A => 1 / ((x : ℝ) * Real.log x)

theorem target : statement := sorry

end Statements.Erdos143SeparatedRealSetSeries
