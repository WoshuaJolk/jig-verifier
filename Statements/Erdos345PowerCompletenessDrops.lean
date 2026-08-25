import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos345PowerCompletenessDrops

/-- Integers representable as sums of distinct positive `k`th powers. -/
def powerSubsetSums (k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ B : Finset ℕ,
    (∀ n ∈ B, 1 ≤ n) ∧ m = ∑ n ∈ B, n ^ k}

/-- The least positive point beyond which every integer is a sum of distinct
positive `k`th powers. -/
noncomputable def threshold (k : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∀ n ≥ m, n ∈ powerSubsetSums k}

/-- Erdős Problem 345: the thresholds decrease infinitely often as the power
is incremented. -/
abbrev statement : Prop :=
  Set.Infinite {k : ℕ | 1 ≤ k ∧ threshold (k + 1) < threshold k}

theorem target : statement := sorry

end Statements.Erdos345PowerCompletenessDrops
