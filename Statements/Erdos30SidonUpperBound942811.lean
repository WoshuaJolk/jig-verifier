import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos30SidonUpperBound942811

/-- Standard unordered-sum uniqueness, including repeated summands. -/
def IsSidon (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A one-sided eventual bound for every finite interval Sidon set. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℤ, A ⊆ Finset.Ico 0 (N : ℤ) → IsSidon A →
      (A.card : ℝ) ≤ Real.sqrt N +
        (942811 / 1000000 : ℝ) * Real.sqrt (Real.sqrt N) + C

theorem target : statement := sorry

end Statements.Erdos30SidonUpperBound942811
