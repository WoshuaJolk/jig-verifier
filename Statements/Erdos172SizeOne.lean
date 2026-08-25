import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic

namespace Statements.Erdos172SizeOne

/-- The finite sums-and-products claim at target size one. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (color : ℕ → Fin n),
    ∃ A : Finset ℕ, A.card ≥ 1 ∧ ∃ c, ∀ S : Finset A,
      S.Nonempty →
      color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c

theorem target : statement := sorry

end Statements.Erdos172SizeOne
