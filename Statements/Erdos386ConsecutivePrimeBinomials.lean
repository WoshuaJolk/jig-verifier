import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos386ConsecutivePrimeBinomials

open Filter Finset Nat
open scoped BigOperators

/-- Erdős Problem 386: for some fixed nontrivial `k`, infinitely many
binomial coefficients `n.choose k` are products of consecutive primes. -/
abbrev statement : Prop :=
  ∃ k ≥ 2, ∃ᶠ n in atTop,
    k ≤ n - 2 ∧
      ∃ p q : ℕ,
        n.choose k = ∏ i ∈ Ico p q, Nat.nth Nat.Prime i

theorem target : statement := sorry

end Statements.Erdos386ConsecutivePrimeBinomials
