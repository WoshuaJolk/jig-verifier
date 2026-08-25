import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos1002AsymptoticDistribution

open Real Set Filter Finset MeasureTheory Topology

noncomputable def discrepancyAverage (α : ℝ) (n : ℕ) : ℝ :=
  (1 / log n) *
    ∑ k ∈ Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))

/-- Erdős problem 1002: the normalized discrepancy sums for rotations have
an asymptotic distribution function. -/
abbrev statement : Prop :=
  ∃ g : ℝ → ℝ,
    Monotone g ∧
    Tendsto g atBot (𝓝 0) ∧
    Tendsto g atTop (𝓝 1) ∧
    ∀ c : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ |
            α ∈ Ioo (0 : ℝ) 1 ∧ discrepancyAverage α n ≤ c}).toReal)
        atTop (𝓝 (g c))

theorem target : statement := sorry

end Statements.Erdos1002AsymptoticDistribution
