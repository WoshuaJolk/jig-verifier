import Mathlib.Data.Finset.Card

namespace Statements.Erdos643BlockGluing

def Uniform {V : Type} [DecidableEq V]
    (t : ℕ) (F : Finset (Finset V)) : Prop :=
  ∀ A ∈ F, A.card = t

def HasDisjointEqualUnion {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, ∃ D ∈ F,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    A ∪ B = C ∪ D ∧ Disjoint A B ∧ Disjoint C D

abbrev statement : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Finset (Finset V)), Uniform 3 F →
    ∀ (blocks : Finset (Finset V)),
      (∀ A ∈ F, ∃ B ∈ blocks, A ⊆ B) →
      (∀ B ∈ blocks, ∀ C ∈ blocks, 2 ≤ (B ∩ C).card → B = C) →
      (∀ B ∈ blocks, ¬HasDisjointEqualUnion (F.filter (fun A => A ⊆ B))) →
      ¬HasDisjointEqualUnion F

theorem target : statement := sorry

end Statements.Erdos643BlockGluing
