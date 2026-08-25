import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped ArithmeticFunction.sigma

namespace Statements.Erdos826FiniteBoxUniformBound

/-- Every finite box of starting values admits one positive linear constant that controls every positive shift. -/
abbrev statement : Prop :=
  ∀ N : ℕ, ∃ C > (0 : ℝ),
    ∀ n ≤ N, ∀ k ≥ 1,
      σ 0 (n + k) ≤ C * k

theorem target : statement := sorry

end Statements.Erdos826FiniteBoxUniformBound
