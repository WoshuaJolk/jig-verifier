import Mathlib.Data.Finset.Card

namespace Submissions.Erdos1145RepresentationCeiling.FalseHypothesis

noncomputable def repCount (A B : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ B).card

theorem proof :
    False →
      ∀ A B : Set ℕ, ∀ n : ℕ, repCount A B n ≤ n + 1 :=
  False.elim

end Submissions.Erdos1145RepresentationCeiling.FalseHypothesis
