import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos951ConsecutiveGeneratorGap

def beurlingInteger (a : ℕ → ℝ) (k : ℕ →₀ ℕ) : ℝ :=
  k.prod fun i e ↦ (a i) ^ e

def Separated (a : ℕ → ℝ) : Prop :=
  ∀ k l : ℕ →₀ ℕ, k ≠ l →
    |beurlingInteger a k - beurlingInteger a l| ≥ 1

/-- Separation of generalized integers forces consecutive generators
to be at least one apart. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℝ, StrictMono a → Separated a →
    ∀ n : ℕ, 1 ≤ a (n + 1) - a n

theorem target : statement := sorry

end Statements.Erdos951ConsecutiveGeneratorGap
