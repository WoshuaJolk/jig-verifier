import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter
open scoped BigOperators

/-!
# Erdős problem 663

For each fixed `k ≥ 2`, is the least prime missing from the product of
`n+1,...,n+k` at most `(1+o(1)) log n`?
-/

namespace Statements.Erdos663LeastMissingPrime

def blockProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∃ p : ℕ, p.Prime ∧
          ¬p ∣ blockProduct n k ∧
          (p : ℝ) < (1 + ε) * Real.log n

theorem target : statement := sorry

end Statements.Erdos663LeastMissingPrime
