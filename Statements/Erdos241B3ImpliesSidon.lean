import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos241B3ImpliesSidon

open Finset

def UniqueRSums (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ m₁ m₂ : Multiset ℕ,
    m₁.card = r → m₂.card = r →
    (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
    m₁.sum = m₂.sum → m₁ = m₂

/-- Every nonempty set with unique three-term multiset sums also has unique
two-term multiset sums. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → UniqueRSums 3 A → UniqueRSums 2 A

theorem target : statement := sorry

end Statements.Erdos241B3ImpliesSidon
