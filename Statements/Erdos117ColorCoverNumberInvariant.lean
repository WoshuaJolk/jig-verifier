import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos117ColorCoverNumberInvariant

def IsIndependentCover {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (C : Finset (Finset α)) : Prop :=
  (∀ x : α, ∃ S ∈ C, x ∈ S) ∧
  (∀ S ∈ C, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y)

noncomputable def colorCoverNumber {α : Type*} [DecidableEq α]
    (R : α → α → Prop) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset α),
    C.card = k ∧ IsIndependentCover R C}

/-- A relation-preserving equivalence identifies the least cardinalities of
finite independent covers. This composes color transport with the minima
bridge in arXiv:2608.20507v1, Lemma 2.1, TeX lines 107--109. -/
abbrev statement : Prop :=
  ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
    (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β),
    (∀ x y, R x y ↔ Q (e x) (e y)) →
    (∃ C : Finset (Finset α), IsIndependentCover R C) →
    colorCoverNumber R = colorCoverNumber Q

theorem target : statement := sorry

end Statements.Erdos117ColorCoverNumberInvariant
