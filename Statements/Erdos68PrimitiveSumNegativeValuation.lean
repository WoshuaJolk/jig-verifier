import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos68PrimitiveSumNegativeValuation

/-- A prime that divides exactly one denominator `N! - 1` in the truncation
through `N` gives the finite reciprocal sum strictly negative `p`-adic
valuation. -/
abbrev statement : Prop :=
  ∀ N p : ℕ, 2 ≤ N → p.Prime → p ∣ N.factorial - 1 →
    (∀ n : ℕ, 2 ≤ n → n < N → ¬p ∣ n.factorial - 1) →
    padicValRat p
        (∑ n ∈ Finset.Icc 2 N,
          (1 : ℚ) / (n.factorial - 1 : ℕ)) < 0

theorem target : statement := sorry

end Statements.Erdos68PrimitiveSumNegativeValuation
