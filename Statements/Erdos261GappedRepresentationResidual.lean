import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos261GappedRepresentationResidual

/-- The integers no block of consecutive indices can represent: `n ≥ 3` and `n`
is not of Borwein--Loring form `2^(k+2) - k - 3`. -/
def BlockUnreachable (n : ℕ) : Prop :=
  3 ≤ n ∧ ∀ k : ℕ, n + k + 3 ≠ 2 ^ (k + 2)

/-- What survives once consecutive-index constructions are ruled out: every
block-unreachable `n` still needs a representation, and any representation it
has must use an index set that is not an interval. -/
abbrev statement : Prop :=
  ∀ n : ℕ, BlockUnreachable n →
    ∃ A : Finset ℕ,
      2 ≤ A.card ∧
      (∀ a ∈ A, 1 ≤ a) ∧
      (n : ℚ) / (2 : ℚ) ^ n = ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a ∧
      ∀ p k : ℕ, A ≠ Finset.Ico p (p + k + 1)

theorem target : statement := sorry

end Statements.Erdos261GappedRepresentationResidual
