import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117ColorCoverNumberInvariant.Control

def IsIndependentCover {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (C : Finset (Finset α)) : Prop :=
  (∀ x : α, ∃ S ∈ C, x ∈ S) ∧
  (∀ S ∈ C, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y)

noncomputable def colorCoverNumber {α : Type*} [DecidableEq α]
    (R : α → α → Prop) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset α),
    C.card = k ∧ IsIndependentCover R C}

theorem proof :
    False →
      ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
        (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β),
        (∀ x y, R x y ↔ Q (e x) (e y)) →
        (∃ C : Finset (Finset α), IsIndependentCover R C) →
        colorCoverNumber R = colorCoverNumber Q := by
  intro h
  exact h.elim

end Submissions.Erdos117ColorCoverNumberInvariant.Control
