import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Erdős problem 963

Must every finite set of reals contain a dissociated subset of cardinality at
least the base-two logarithm of the original cardinality?
-/

namespace Statements.Erdos963DissociatedSubset

def Dissociated (B : Finset ℝ) : Prop :=
  ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B →
    (∑ x ∈ S, x) = ∑ x ∈ T, x → S = T

abbrev statement : Prop :=
  ∀ A : Finset ℝ, ∃ B : Finset ℝ,
    B ⊆ A ∧ Dissociated B ∧ Nat.log 2 A.card ≤ B.card

theorem target : statement := sorry

end Statements.Erdos963DissociatedSubset
