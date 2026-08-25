import Mathlib.Data.Finset.Card

namespace Submissions.Erdos1145RepresentationCeiling.Direct

noncomputable def repCount (A B : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ B).card

theorem proof :
    ∀ A B : Set ℕ, ∀ n : ℕ, repCount A B n ≤ n + 1 := by
  intro A B n
  classical
  unfold repCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

end Submissions.Erdos1145RepresentationCeiling.Direct
