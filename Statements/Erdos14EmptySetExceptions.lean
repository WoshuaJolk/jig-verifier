import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Nat

namespace Statements.Erdos14EmptySetExceptions

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionCount (A : Set ℕ) (N : ℕ) : ℝ :=
  (((Set.Icc 1 N) \ uniquePairSums A).ncard : ℝ)

/-- For the empty set, every positive integer up to `N` is an exception. -/
abbrev statement : Prop :=
  ∀ N : ℕ, exceptionCount ∅ N = (N : ℝ)

theorem target : statement := sorry

end Statements.Erdos14EmptySetExceptions
