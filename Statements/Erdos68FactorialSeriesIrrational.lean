import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos68FactorialSeriesIrrational

/-- Erdős problem 68. -/
abbrev statement : Prop :=
  Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ))

theorem target : statement := sorry

end Statements.Erdos68FactorialSeriesIrrational
