import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos462LeastPrimeFactorShortIntervals

open Filter Finset

noncomputable def upperEndpoint (C : ℝ) (x : ℕ) : ℕ :=
  ⌊(x : ℝ) + C * Real.sqrt x * (Real.log x) ^ 2⌋₊

noncomputable def intervalMass (C : ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Icc x (upperEndpoint C x), (n.minFac : ℝ) / n

/-- Erdős problem 462: a fixed square-root-log-squared interval carries
a uniformly positive mass of least-prime-factor weights. -/
abbrev statement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ᶠ x : ℕ in atTop, c ≤ intervalMass C x

theorem target : statement := sorry

end Statements.Erdos462LeastPrimeFactorShortIntervals
