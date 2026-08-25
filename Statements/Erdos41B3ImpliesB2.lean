import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Sum

namespace Statements.Erdos41B3ImpliesB2

def IsBhSequence (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ I J : Multiset ℕ,
    I.card = h → J.card = h →
    (∀ a ∈ I, a ∈ A) → (∀ a ∈ J, a ∈ A) →
    I.sum = J.sum → I = J

abbrev statement : Prop :=
  ∀ A : Set ℕ, IsBhSequence A 3 → A.Nonempty → IsBhSequence A 2

theorem target : statement := sorry

end Statements.Erdos41B3ImpliesB2
