import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace Statements.Erdos1049ChowlaLambert

/-- Chowla's conjecture: the Lambert series is irrational at every rational
parameter greater than one. -/
abbrev statement : Prop :=
  ∀ t : ℚ, t > 1 →
    Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1))

theorem target : statement := sorry

end Statements.Erdos1049ChowlaLambert
