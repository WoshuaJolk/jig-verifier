import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Statements.Erdos1145PeriodicClosureUnbounded

noncomputable def repCount (A B : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ B).card

/-- Two nonempty sets closed under a common positive translation have an
unbounded ordered representation function. -/
abbrev statement : Prop :=
  ∀ A B : Set ℕ, ∀ q a b : ℕ, 0 < q → a ∈ A → b ∈ B →
    (∀ x ∈ A, x + q ∈ A) →
    (∀ x ∈ B, x + q ∈ B) →
    ∀ K : ℕ, ∃ n : ℕ, K < repCount A B n

theorem target : statement := sorry

end Statements.Erdos1145PeriodicClosureUnbounded
