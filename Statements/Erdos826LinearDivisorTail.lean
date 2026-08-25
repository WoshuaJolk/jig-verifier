import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped ArithmeticFunction.sigma

namespace Statements.Erdos826LinearDivisorTail

/-- Erdős Problem 826: a fixed positive linear bound controls every positive shift of infinitely many starting values. -/
abbrev statement : Prop :=
  ∃ C > (0 : ℝ),
    {n : ℕ | ∀ k ≥ 1, σ 0 (n + k) ≤ C * k}.Infinite

theorem target : statement := sorry

end Statements.Erdos826LinearDivisorTail
