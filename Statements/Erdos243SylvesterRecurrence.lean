import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Rat

open Filter
open scoped Topology

namespace Statements.Erdos243SylvesterRecurrence

/-- Erdős Problem 243: a rapidly growing sequence with rational reciprocal
sum must eventually satisfy the Sylvester recurrence. -/
abbrev statement : Prop :=
  ∀ (a : ℕ → ℕ), StrictMono a →
    Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1) →
    Summable ((1 : ℚ) / a ·) →
    ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1

theorem target : statement := sorry

end Statements.Erdos243SylvesterRecurrence
