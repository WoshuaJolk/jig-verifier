import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Statements.Erdos329EmptySidon

def IsSidon (A : Set ℕ) : Prop :=
  ∀ I J : Multiset ℕ,
    I.card = 2 → J.card = 2 →
    (∀ a ∈ I, a ∈ A) → (∀ a ∈ J, a ∈ A) →
    I.sum = J.sum → I = J

/-- The empty set satisfies the multiset formulation of the Sidon property. -/
abbrev statement : Prop :=
  IsSidon (∅ : Set ℕ)

theorem target : statement := sorry

end Statements.Erdos329EmptySidon
