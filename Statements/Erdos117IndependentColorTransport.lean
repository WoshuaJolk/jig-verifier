import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace Statements.Erdos117IndependentColorTransport

def IsIndependentCover {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (C : Finset (Finset α)) : Prop :=
  (∀ x : α, ∃ S ∈ C, x ∈ S) ∧
  (∀ S ∈ C, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y)

def transportColors {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : Finset (Finset α)) : Finset (Finset β) :=
  C.image (fun S ↦ S.image e)

/-- The graph-isomorphism color-transport step from arXiv:2608.20507v1,
Lemma 2.1, TeX lines 107--109. -/
abbrev statement : Prop :=
  ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
    (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β),
    (∀ x y, R x y ↔ Q (e x) (e y)) →
    ∀ C : Finset (Finset α),
      IsIndependentCover R C →
      IsIndependentCover Q (transportColors e C) ∧
        (transportColors e C).card = C.card

theorem target : statement := sorry

end Statements.Erdos117IndependentColorTransport
