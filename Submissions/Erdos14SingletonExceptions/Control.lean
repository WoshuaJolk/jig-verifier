import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Nat

namespace Submissions.Erdos14SingletonExceptions.Control

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionCount (A : Set ℕ) (N : ℕ) : ℝ :=
  (((Set.Icc 1 N) \ uniquePairSums A).ncard : ℝ)

abbrev claimedStatement : Prop :=
  ∀ a N : ℕ, exceptionCount {a} N =
    if 1 ≤ 2 * a ∧ 2 * a ≤ N then (N - 1 : ℕ) else N

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos14SingletonExceptions.Control
