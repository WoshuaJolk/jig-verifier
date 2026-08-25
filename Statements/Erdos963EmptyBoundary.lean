import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Statements.Erdos963EmptyBoundary

def Dissociated (B : Finset ℝ) : Prop :=
  ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B →
    (∑ x ∈ S, x) = ∑ x ∈ T, x → S = T

abbrev statement : Prop :=
  Dissociated ∅

theorem target : statement := sorry

end Statements.Erdos963EmptyBoundary
