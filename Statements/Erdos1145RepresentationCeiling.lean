import Mathlib.Data.Finset.Card

namespace Statements.Erdos1145RepresentationCeiling

noncomputable def repCount (A B : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ B).card

/-- There are at most `n+1` ordered natural representations of `n`. -/
abbrev statement : Prop :=
  ∀ A B : Set ℕ, ∀ n : ℕ, repCount A B n ≤ n + 1

theorem target : statement := sorry

end Statements.Erdos1145RepresentationCeiling
