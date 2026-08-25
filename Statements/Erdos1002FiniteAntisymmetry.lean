import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos1002FiniteAntisymmetry

open Real Finset

noncomputable def discrepancyAverage (α : ℝ) (n : ℕ) : ℝ :=
  (1 / log n) *
    ∑ k ∈ Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))

/-- Away from the finite rational exceptional set, the finite normalized
discrepancy statistic is odd under `α ↦ 1 - α`. -/
abbrev statement : Prop :=
  ∀ α : ℝ, ∀ n : ℕ,
    (∀ k ∈ Icc (1 : ℕ) n, Int.fract (α * k) ≠ 0) →
    discrepancyAverage (1 - α) n = -discrepancyAverage α n

theorem target : statement := sorry

end Statements.Erdos1002FiniteAntisymmetry
