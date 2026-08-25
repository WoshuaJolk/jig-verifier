import Mathlib.Data.Nat.Basic

namespace Statements.Erdos645LargeDifferenceAP

abbrev statement : Prop :=
  ∀ c : ℕ → Bool, ∃ x d, 0 < x ∧ x < d ∧
    ∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C

theorem target : statement := sorry

end Statements.Erdos645LargeDifferenceAP
