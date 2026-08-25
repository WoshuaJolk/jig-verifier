import Mathlib.Data.Finset.Sum
import Mathlib.Data.List.Basic
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos338RobustBasisRestrictedOrder

open Filter
open scoped BigOperators

def IsBasis (A : Set ℕ) : Prop :=
  ∃ h : ℕ, ∀ᶠ n in atTop,
    ∃ terms : List ℕ,
      terms.length = h ∧ (∀ a ∈ terms, a ∈ A) ∧ terms.sum = n

def IsRobustBasis (A : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, ↑F ⊆ A → IsBasis (A \ F)

def HasRestrictedOrder (A : Set ℕ) : Prop :=
  ∃ t : ℕ, ∀ᶠ n in atTop,
    ∃ terms : Finset ℕ,
      terms.card ≤ t ∧ ↑terms ⊆ A ∧ ∑ a ∈ terms, a = n

/-- The concrete robust-basis question in Erdős Problem 338:
deleting any finite subset while retaining a basis forces a restricted order. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, IsRobustBasis A → HasRestrictedOrder A

theorem target : statement := sorry

end Statements.Erdos338RobustBasisRestrictedOrder
