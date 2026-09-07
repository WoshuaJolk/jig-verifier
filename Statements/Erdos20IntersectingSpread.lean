import Mathlib.Data.Set.Card

namespace Statements.Erdos20IntersectingSpread

/-- At every natural spread parameter there is a finite nonempty uniform family
whose members all intersect. Spread refers to the uniform distribution on F. -/
abbrev statement : Prop :=
  ∀ κ : ℕ, 2 ≤ κ →
    ∃ (α : Type) (w : ℕ) (F : Set (Set α)),
      0 < w ∧ F.Finite ∧ F.Nonempty ∧
      (∀ A ∈ F, A.ncard = w) ∧
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
      (∀ S : Set α, {A ∈ F | S ⊆ A}.ncard * κ ^ S.ncard ≤ F.ncard)

theorem target : statement := sorry

end Statements.Erdos20IntersectingSpread
