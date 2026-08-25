import Mathlib.Data.Set.Card

namespace Statements.Erdos602AlmostDisjointPropertyB

def IsMonochromatic {α : Type*} (f : α → Fin 2) (A : Set α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, f x = f y

def HasPropertyB {α : Type*} (I : Type*) (A : I → Set α) : Prop :=
  ∃ f : α → Fin 2, ∀ i, ¬IsMonochromatic f (A i)

/-- Erdős Problem 602: an almost-disjoint family of countably infinite sets
with no singleton pairwise intersection has Property B. -/
abbrev statement : Prop :=
  ∀ {α : Type*} {I : Type*} (A : I → Set α),
    (∀ i, (A i).Countable ∧ (A i).Infinite) →
    (∀ i j, i ≠ j → (A i ∩ A j).Finite) →
    (∀ i j, i ≠ j → Set.ncard (A i ∩ A j) ≠ 1) →
    HasPropertyB I A

theorem target : statement := sorry

end Statements.Erdos602AlmostDisjointPropertyB
