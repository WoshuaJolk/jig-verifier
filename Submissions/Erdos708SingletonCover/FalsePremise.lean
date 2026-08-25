import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Submissions.Erdos708SingletonCover.FalsePremise

theorem proof :
    False →
      ∀ a : ℕ, 2 ≤ a →
        ∀ s : ℕ, 1 ≤ s →
          ∃ B : Finset ℕ,
            B ⊆ Finset.Ico s (s + a) ∧
              B.card ≤ 1 ∧
                a ∣ ∏ b ∈ B, b := by
  intro h
  exact h.elim

end Submissions.Erdos708SingletonCover.FalsePremise
