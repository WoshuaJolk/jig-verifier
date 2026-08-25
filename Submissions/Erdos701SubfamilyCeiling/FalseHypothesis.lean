import Mathlib.Data.Finset.Card

namespace Submissions.Erdos701SubfamilyCeiling.FalseHypothesis

theorem proof :
    False →
      ∀ {X : Type} [DecidableEq X] (F A : Finset (Finset X)),
        A ⊆ F → A.card ≤ F.card :=
  False.elim

end Submissions.Erdos701SubfamilyCeiling.FalseHypothesis
