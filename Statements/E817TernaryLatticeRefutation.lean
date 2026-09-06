import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace Statements.E817TernaryLatticeRefutation

open Filter

def subsetSums (A : Finset ℕ) : Set ℕ :=
  {x | ∃ B ⊆ A, ∑ a ∈ B, a = x}

def IsThreeAPFree (S : Set ℕ) : Prop :=
  ∀ x y z, x ∈ S → y ∈ S → z ∈ S → x + z = 2 * y → x = z

def Admissible (n N : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = n ∧
    IsThreeAPFree (subsetSums A)

noncomputable def g (n : ℕ) : ℕ :=
  sInf {N | Admissible n N}

/-- Literal negation of the central base-three lower-bound conjecture. -/
abbrev statement : Prop :=
  ¬ ((fun n : ℕ ↦ (3 ^ n : ℝ)) =O[atTop] fun n ↦ (g n : ℝ))

theorem target : statement := sorry

end Statements.E817TernaryLatticeRefutation
