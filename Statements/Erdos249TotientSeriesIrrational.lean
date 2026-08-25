import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Statements.Erdos249TotientSeriesIrrational

noncomputable def totientSeries : ℝ :=
  ∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n

/-- Erdős Problem 249: the binary Euler-totient series is irrational. -/
abbrev statement : Prop :=
  Irrational totientSeries

theorem target : statement := sorry

end Statements.Erdos249TotientSeriesIrrational
