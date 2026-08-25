import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real

namespace Statements.Erdos249SeriesConvergenceBoundary

noncomputable def term (n : ℕ) : ℝ :=
  (Nat.totient n : ℝ) / (2 : ℝ) ^ n

/-- The explicit real-valued totient series is absolutely summable,
and its added natural-number index zero contributes nothing. -/
abbrev statement : Prop :=
  Summable term ∧ term 0 = 0

theorem target : statement := sorry

end Statements.Erdos249SeriesConvergenceBoundary
