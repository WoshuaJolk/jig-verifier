import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Statements.Erdos44ShiftCollisionBound

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

abbrev ShiftWitness := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

/-- Canonical ordered witnesses to a mixed/block collision
`a + (t+c) = 2t + c₁+c₂`.  The order `c₁ ≤ c₂` removes the
irrelevant interchange of the two block summands. -/
def ShiftCollisions (S A C : Finset ℕ) : Finset ShiftWitness :=
  ((((S ×ˢ A) ×ˢ C) ×ˢ C) ×ˢ C).filter fun p =>
    p.1.2 ≤ p.2 ∧
      p.1.1.1.2 + (p.1.1.1.1 + p.1.1.2) =
        2 * p.1.1.1.1 + p.1.2 + p.2

/-- Across any finite window `S` of candidate shifts, a Sidon block has at most
`|S||A||C|` canonical mixed/block collisions. -/
abbrev statement : Prop :=
  ∀ (S A C : Finset ℕ), IsSidon (C : Set ℕ) →
    (ShiftCollisions S A C).card ≤ S.card * A.card * C.card

theorem target : statement := by
  sorry

end Statements.Erdos44ShiftCollisionBound
