import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Card

namespace Statements.Erdos172FiniteSumsProducts

/-- The finite sums-and-products conjecture of Hindman, Erdős Problem 172. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (color : ℕ → Fin n) (m : ℕ),
    ∃ A : Finset ℕ, A.card ≥ m ∧ ∃ c, ∀ S : Finset A,
      S.Nonempty →
      color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c

theorem target : statement := sorry

end Statements.Erdos172FiniteSumsProducts
