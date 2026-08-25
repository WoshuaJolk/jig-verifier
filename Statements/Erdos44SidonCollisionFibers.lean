import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Statements.Erdos44SidonCollisionFibers

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

abbrev Triple := (ℕ × ℕ) × ℕ

def IsCollision (C : Finset ℕ) (d : ℕ) (p : Triple) : Prop :=
  p.1.1 ∈ C ∧ p.1.2 ∈ C ∧ p.2 ∈ C ∧
    p.1.1 + p.1.2 = d + p.2

/-- At a nonexceptional offset, the three coordinate fibers of the Sidon
collision hypergraph have sizes at most one, one, and two. -/
abbrev statement : Prop :=
  ∀ (C : Finset ℕ), IsSidon (C : Set ℕ) →
    ∀ d ∉ C,
      (∀ p q : Triple, IsCollision C d p → IsCollision C d q →
        p.1.1 = q.1.1 → p = q) ∧
      (∀ p q : Triple, IsCollision C d p → IsCollision C d q →
        p.1.2 = q.1.2 → p = q) ∧
      (∀ p q : Triple, IsCollision C d p → IsCollision C d q →
        p.2 = q.2 →
          (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) ∨
          (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1))

theorem target : statement := by
  sorry

end Statements.Erdos44SidonCollisionFibers
