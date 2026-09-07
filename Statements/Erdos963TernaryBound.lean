import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Statements.Erdos963TernaryBound

def Dissociated (B : Finset ℝ) : Prop :=
  ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B →
    (∑ x ∈ S, x) = ∑ x ∈ T, x → S = T

abbrev statement : Prop :=
  ∀ A : Finset ℝ, ∃ B : Finset ℝ,
    B ⊆ A ∧ Dissociated B ∧ A.card ≤ 3 ^ B.card

theorem target : statement := sorry

end Statements.Erdos963TernaryBound
