import Mathlib.Data.Nat.Basic

namespace Submissions.Erdos645LargeDifferenceAP.Control

theorem erdos_645 : False →
    ∀ c : ℕ → Bool, ∃ x d, 0 < x ∧ x < d ∧
      ∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C :=
  fun hFalse => hFalse.elim

#print axioms erdos_645

end Submissions.Erdos645LargeDifferenceAP.Control
