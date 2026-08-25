import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Asymptotics Filter
open scoped Real

namespace Statements.Erdos367PowerfulPartProduct

/-- The `r`-full part of `n`: retain exactly those prime powers in the
factorization whose exponent is at least `r`. -/
def fullPart (r n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support with r ≤ n.factorization p,
    p ^ n.factorization p

/-- Erdős Problem 367(i): every fixed consecutive block has product of
2-full parts at most `n^(2+o(1))`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ e : ℕ → ℝ,
      e =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop,
        ((∏ m ∈ Finset.Ico n (n + k), fullPart 2 m : ℕ) : ℝ) ≤
          (n : ℝ) ^ (2 + e n)

theorem target : statement := sorry

end Statements.Erdos367PowerfulPartProduct
