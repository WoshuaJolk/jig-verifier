import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Pointwise BigOperators

namespace Statements.Erdos52GcdGroupProducts

abbrev statement : Prop :=
    ∀ (S : ℕ) (A G : Finset ℕ) (B : ℕ → Finset ℕ) (m : ℕ → ℕ),
      (∀ g ∈ G, B g ⊆ A) →
      (∀ g ∈ G, ∀ x ∈ B g, Nat.gcd S x = g) →
      (∀ g ∈ G, m g + (m g).choose 2 ≤ (B g * B g).card) →
      (∑ g ∈ G, (m g + (m g).choose 2)) ≤ (A * A).card

theorem target : statement := sorry

end Statements.Erdos52GcdGroupProducts
