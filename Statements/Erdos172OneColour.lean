import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic

namespace Statements.Erdos172OneColour

/-- The finite sums-and-products claim for a one-colour colouring. -/
abbrev statement : Prop :=
  ∀ (color : ℕ → Fin 1) (m : ℕ),
    ∃ A : Finset ℕ, A.card ≥ m ∧ ∃ c, ∀ S : Finset A,
      S.Nonempty →
      color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c

theorem target : statement := sorry

end Statements.Erdos172OneColour
