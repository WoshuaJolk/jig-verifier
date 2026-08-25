import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Submissions.Erdos44TwoOffsetCoverBarrier.Direct

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

theorem proof :
    ∀ {α : Type*} [AddCommGroup α] [DecidableEq α]
      (A C : Finset α), OffsetCoverBarrier C → CrossUnique A C →
        ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ →
          ∀ t X, CoversAllOffsets A C t X → C.card ≤ 4 * X.card := by
  intro α _ _ A C hbarrier hcross a₁ ha₁ a₂ ha₂ hne t X hcovers
  by_cases h₁ : t - a₁ ∈ C
  · have h₂ : t - a₂ ∉ C := by
      intro h₂
      have heq : a₁ + (t - a₁) = a₂ + (t - a₂) := by abel
      exact hne (hcross a₁ ha₁ a₂ ha₂ (t - a₁) h₁ (t - a₂) h₂ heq).1
    exact hbarrier (t - a₂) h₂ X (hcovers a₂ ha₂)
  · exact hbarrier (t - a₁) h₁ X (hcovers a₁ ha₁)

end Submissions.Erdos44TwoOffsetCoverBarrier.Direct
