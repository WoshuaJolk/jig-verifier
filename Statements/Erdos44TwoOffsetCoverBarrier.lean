import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Statements.Erdos44TwoOffsetCoverBarrier

open Set Finset

abbrev Triple (α : Type*) := (α × α) × α

def CollisionTriples {α : Type*} [AddCommGroup α] [DecidableEq α]
    (C : Finset α) (d : α) : Finset (Triple α) :=
  ((C ×ˢ C) ×ˢ C).filter fun p => p.1.1 + p.1.2 - p.2 = d

def Covers {α : Type*} [AddCommGroup α] [DecidableEq α]
    (C : Finset α) (d : α) (X : Finset α) : Prop :=
  (CollisionTriples C d).filter
    (fun p => p.1.1 ∈ X ∨ p.1.2 ∈ X ∨ p.2 ∈ X) =
      CollisionTriples C d

def CrossUnique {α : Type*} [AddCommGroup α]
    (A C : Finset α) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ c₁ ∈ C, ∀ c₂ ∈ C,
    a₁ + c₁ = a₂ + c₂ → a₁ = a₂ ∧ c₁ = c₂

def OffsetCoverBarrier {α : Type*} [AddCommGroup α] [DecidableEq α]
    (C : Finset α) : Prop :=
  ∀ d ∉ C, ∀ X : Finset α, Covers C d X → C.card ≤ 4 * X.card

def CoversAllOffsets {α : Type*} [AddCommGroup α] [DecidableEq α]
    (A C : Finset α) (t : α) (X : Finset α) : Prop :=
  ∀ a ∈ A, Covers C (t - a) X

/-- Two distinct old points and cross-sum injectivity force every shift to have
at least one nonexceptional collision offset. -/
abbrev statement : Prop :=
  ∀ {α : Type*} [AddCommGroup α] [DecidableEq α]
    (A C : Finset α), OffsetCoverBarrier C → CrossUnique A C →
      ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ →
        ∀ t X, CoversAllOffsets A C t X → C.card ≤ 4 * X.card

theorem target : statement := by
  sorry

end Statements.Erdos44TwoOffsetCoverBarrier
