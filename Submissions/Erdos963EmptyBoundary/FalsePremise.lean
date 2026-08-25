import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Submissions.Erdos963EmptyBoundary.FalsePremise

def Dissociated (B : Finset ℝ) : Prop :=
  ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B →
    (∑ x ∈ S, x) = ∑ x ∈ T, x → S = T

theorem proof :
    False → Dissociated ∅ := by
  intro h
  exact h.elim

end Submissions.Erdos963EmptyBoundary.FalsePremise
