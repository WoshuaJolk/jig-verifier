import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic

open Set
open scoped Polynomial

namespace Statements.Erdos906CofiniteDerivativeZeros

/-- A source-faithful formulation of Erdős Problem 906: a transcendental entire function whose
zero sets are dense along every strictly increasing sequence of derivative orders. -/
abbrev statement : Prop :=
  ∃ f : ℂ → ℂ,
    f ≠ 0 ∧
    AnalyticOnNhd ℂ f Set.univ ∧
    (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
    ∀ s : ℕ → ℕ, StrictMono s →
      Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0}

theorem target : statement := sorry

end Statements.Erdos906CofiniteDerivativeZeros
