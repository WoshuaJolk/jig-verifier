import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Nth

namespace Statements.Erdos233ZeroGapSquareSum

open scoped BigOperators

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- The empty initial segment of squared prime gaps has sum zero. -/
abbrev statement : Prop :=
  (∑ n ∈ Finset.range 0, (primeGap n) ^ 2 : ℕ) = 0

theorem target : statement := sorry

end Statements.Erdos233ZeroGapSquareSum
