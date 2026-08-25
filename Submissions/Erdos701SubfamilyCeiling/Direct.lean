import Mathlib.Data.Finset.Card

namespace Submissions.Erdos701SubfamilyCeiling.Direct

theorem proof :
    ∀ {X : Type} [DecidableEq X] (F A : Finset (Finset X)),
      A ⊆ F → A.card ≤ F.card := by
  intro X _ F A h
  exact Finset.card_le_card h

end Submissions.Erdos701SubfamilyCeiling.Direct
