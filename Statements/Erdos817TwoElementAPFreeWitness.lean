import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos817TwoElementAPFreeWitness

def subsetSums (A : Finset ℕ) : Set ℕ :=
  {x | ∃ B ⊆ A, ∑ a ∈ B, a = x}

def IsThreeAPFree (S : Set ℕ) : Prop :=
  ∀ x y z, x ∈ S → y ∈ S → z ∈ S → x + z = 2 * y → x = z

def Admissible (n N : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = n ∧
    IsThreeAPFree (subsetSums A)

/-- The set `{2,3} ⊆ [1,3]` has subset sums `{0,2,3,5}`, which contain no
nontrivial three-term arithmetic progression. -/
abbrev statement : Prop :=
  Admissible 2 3

theorem target : statement := sorry

end Statements.Erdos817TwoElementAPFreeWitness
