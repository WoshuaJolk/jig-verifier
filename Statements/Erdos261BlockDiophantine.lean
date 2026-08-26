import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos261BlockDiophantine

/-- The Erdős--Graham equation restricted to a block of consecutive indices.
`n` is represented by `A = {n+p, …, n+p+k}` exactly when the shifted sum
`∑_{b=p}^{p+k} (n+b)/2^b` equals `n`. -/
abbrev statement : Prop :=
  ∀ n p k : ℕ,
    (∑ b ∈ Finset.Ico p (p + k + 1), ((n : ℚ) + b) / (2 : ℚ) ^ b = (n : ℚ))
      ↔ 2 ^ (k + 1) * (n + p + 1) = n * (2 ^ (p + k) + 1) + (p + k) + 2

theorem target : statement := sorry

end Statements.Erdos261BlockDiophantine
