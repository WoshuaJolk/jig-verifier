import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos345FirstPowerThreshold

def powerSubsetSums (k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ B : Finset ℕ,
    (∀ n ∈ B, 1 ≤ n) ∧ m = ∑ n ∈ B, n ^ k}

noncomputable def threshold (k : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∀ n ≥ m, n ∈ powerSubsetSums k}

/-- The threshold for distinct positive first powers is one. -/
abbrev statement : Prop := threshold 1 = 1

theorem target : statement := sorry

end Statements.Erdos345FirstPowerThreshold
