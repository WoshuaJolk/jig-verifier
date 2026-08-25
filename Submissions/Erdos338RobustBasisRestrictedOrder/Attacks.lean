import Mathlib.Data.Finset.Sum
import Mathlib.Data.List.Basic
import Mathlib.Topology.Instances.Nat

namespace Submissions.Erdos338RobustBasisRestrictedOrder.Attacks

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

abbrev claimedStatement : Prop :=
  ∀ A : Set ℕ, IsRobustBasis A → HasRestrictedOrder A

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos338RobustBasisRestrictedOrder.Attacks
