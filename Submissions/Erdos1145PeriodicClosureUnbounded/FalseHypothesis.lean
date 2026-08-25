import Mathlib.Data.Finset.Card

namespace Submissions.Erdos1145PeriodicClosureUnbounded.FalseHypothesis

noncomputable def repCount (A B : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ B).card

theorem proof :
    False →
      ∀ A B : Set ℕ, ∀ q a b : ℕ, 0 < q → a ∈ A → b ∈ B →
        (∀ x ∈ A, x + q ∈ A) →
        (∀ x ∈ B, x + q ∈ B) →
        ∀ K : ℕ, ∃ n : ℕ, K < repCount A B n :=
  False.elim

end Submissions.Erdos1145PeriodicClosureUnbounded.FalseHypothesis
