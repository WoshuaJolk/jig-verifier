import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card

namespace Statements.Erdos643CommonLinkReduction

def Uniform {V : Type} [DecidableEq V]
    (t : ℕ) (F : Finset (Finset V)) : Prop :=
  ∀ A ∈ F, A.card = t

def HasDisjointEqualUnion {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, ∃ D ∈ F,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    A ∪ B = C ∪ D ∧ Disjoint A B ∧ Disjoint C D

/-- An edge of the graph common to the links of u and v. -/
def CommonLinkPair {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) (u v : V) (P : Finset V) : Prop :=
  P.card = 2 ∧ u ∉ P ∧ v ∉ P ∧ insert u P ∈ F ∧ insert v P ∈ F

abbrev statement : Prop :=
  ∀ (V : Type) [DecidableEq V] (F : Finset (Finset V)), Uniform 3 F →
    (¬HasDisjointEqualUnion F ↔
      ∀ u v : V, u ≠ v → ∀ P Q : Finset V,
        CommonLinkPair F u v P → CommonLinkPair F u v Q → ¬Disjoint P Q)

theorem target : statement := sorry

end Statements.Erdos643CommonLinkReduction
