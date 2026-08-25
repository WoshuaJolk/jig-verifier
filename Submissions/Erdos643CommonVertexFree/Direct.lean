import Mathlib.Data.Finset.BooleanAlgebra

namespace Submissions.Erdos643CommonVertexFree.Direct

def HasDisjointEqualUnion {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, ∃ D ∈ F,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    A ∪ B = C ∪ D ∧ Disjoint A B ∧ Disjoint C D

theorem proof :
    ∀ (V : Type) [DecidableEq V],
      ∀ F : Finset (Finset V), ∀ v : V,
        (∀ A ∈ F, v ∈ A) → ¬HasDisjointEqualUnion F := by
  intro V inst F v hv
  rintro ⟨A, hA, B, hB, C, hC, D, hD,
    hABn, hAC, hAD, hBC, hBD, hCDn, hunion, hAB, hCD⟩
  exact Finset.disjoint_left.mp hAB (hv A hA) (hv B hB)

end Submissions.Erdos643CommonVertexFree.Direct
