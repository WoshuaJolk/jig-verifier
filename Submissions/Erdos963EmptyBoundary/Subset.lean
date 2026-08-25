import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Submissions.Erdos963EmptyBoundary.Subset

def Dissociated (B : Finset ℝ) : Prop :=
  ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B →
    (∑ x ∈ S, x) = ∑ x ∈ T, x → S = T

theorem proof :
    Dissociated ∅ := by
  intro S T hS hT hsum
  have hS0 : S = ∅ := Finset.Subset.antisymm hS (by simp)
  have hT0 : T = ∅ := Finset.Subset.antisymm hT (by simp)
  exact hS0.trans hT0.symm

end Submissions.Erdos963EmptyBoundary.Subset
