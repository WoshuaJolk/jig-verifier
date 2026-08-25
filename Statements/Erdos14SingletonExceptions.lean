import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Nat

namespace Statements.Erdos14SingletonExceptions

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionCount (A : Set ℕ) (N : ℕ) : ℝ :=
  (((Set.Icc 1 N) \ uniquePairSums A).ncard : ℝ)

/-- A singleton has only the unique sum `a + a`; all other positive
integers up to `N` are exceptions. -/
abbrev statement : Prop :=
  ∀ a N : ℕ, exceptionCount {a} N =
    if 1 ≤ 2 * a ∧ 2 * a ≤ N then (N - 1 : ℕ) else N

theorem target : statement := sorry

end Statements.Erdos14SingletonExceptions
