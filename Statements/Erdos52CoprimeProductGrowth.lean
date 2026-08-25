import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic

open scoped Pointwise

namespace Statements.Erdos52CoprimeProductGrowth

/--
A pairwise-coprime upper layer and a smaller positive lower layer have
collision-free cross-products, giving a product-set lower bound after
embedding the ambient natural-number set into the integers.
-/
abbrev statement : Prop :=
  ∀ A P B : Finset ℕ,
    P ⊆ A →
    B ⊆ A →
    (∀ p ∈ P, 0 < p) →
    (∀ b ∈ B, 0 < b) →
    (∀ p ∈ P, ∀ b ∈ B, b < p) →
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Nat.Coprime p q) →
    P.card * B.card ≤
      ((A.image fun n : ℕ => (n : ℤ)) *
        (A.image fun n : ℕ => (n : ℤ))).card

theorem target : statement := sorry

end Statements.Erdos52CoprimeProductGrowth
