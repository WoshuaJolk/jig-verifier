import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos30SidonUpperBoundSqrtEightNinths

/-- Standard unordered-sum uniqueness, including repeated summands. -/
def IsSidon (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

abbrev statement : Prop :=
  ∀ N : ℕ, 2^24 ≤ N → ∀ A : Finset ℤ,
    A ⊆ Finset.Ico 0 (N : ℤ) → IsSidon A →
      (A.card : ℝ) ≤ Real.sqrt N +
        Real.sqrt ((8:ℝ)/9) * Real.sqrt (Real.sqrt N) + 22

theorem target : statement := sorry
end Statements.Erdos30SidonUpperBoundSqrtEightNinths
