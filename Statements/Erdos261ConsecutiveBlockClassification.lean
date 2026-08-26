import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos261ConsecutiveBlockClassification

/-- Every representation of a positive integer in the Erdős--Graham equation
whose index set is a block of consecutive integers `{n+p, …, n+p+k}` with
`p ≥ 1` is Borwein--Loring (`p = 1`, `n = 2^(k+2) - k - 3`), or one of exactly
two sporadic blocks: `A = {4,5,6}` for `n = 2` and `A = {4,5,6}` for `n = 1`. -/
abbrev statement : Prop :=
  ∀ n p k : ℕ, 1 ≤ n → 1 ≤ p →
    (∑ b ∈ Finset.Ico p (p + k + 1), ((n : ℚ) + b) / (2 : ℚ) ^ b = (n : ℚ)) →
    (p = 1 ∧ n + k + 3 = 2 ^ (k + 2)) ∨
    (p = 2 ∧ k = 2 ∧ n = 2) ∨
    (p = 3 ∧ k = 2 ∧ n = 1)

theorem target : statement := sorry

end Statements.Erdos261ConsecutiveBlockClassification
