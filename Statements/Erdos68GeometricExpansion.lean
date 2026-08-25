import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.Erdos68GeometricExpansion

/-- Expand each reciprocal `1 / (n! - 1)` as its geometric series. -/
abbrev statement : Prop :=
  let f (n k : ℕ) : ℝ := 1 / ((n + 2).factorial : ℝ) ^ (k + 1)
  ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1) =
    ∑' n : ℕ, ∑' k : ℕ, f n k

theorem target : statement := sorry

end Statements.Erdos68GeometricExpansion
