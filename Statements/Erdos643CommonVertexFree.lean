import Mathlib.Data.Finset.BooleanAlgebra

namespace Statements.Erdos643CommonVertexFree

def HasDisjointEqualUnion {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, ∃ D ∈ F,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    A ∪ B = C ∪ D ∧ Disjoint A B ∧ Disjoint C D

abbrev statement : Prop :=
  ∀ (V : Type) [DecidableEq V],
    ∀ F : Finset (Finset V), ∀ v : V,
      (∀ A ∈ F, v ∈ A) → ¬HasDisjointEqualUnion F

theorem target : statement := sorry

end Statements.Erdos643CommonVertexFree
