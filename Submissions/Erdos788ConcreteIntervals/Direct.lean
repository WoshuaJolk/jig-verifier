import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Submissions.Erdos788ConcreteIntervals.Direct

def InUpperInterval (n : ℕ) (B : Finset ℕ) : Prop :=
  ∀ b ∈ B, 2 * n < b ∧ b < 4 * n

def InLowerInterval (n : ℕ) (C : Finset ℕ) : Prop :=
  ∀ c ∈ C, n < c ∧ c < 2 * n

def AvoidsDistinctSums (B C : Finset ℕ) : Prop :=
  ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B

theorem proof :
    InUpperInterval 1 {3} ∧
      InLowerInterval 3 {4, 5} ∧
        AvoidsDistinctSums {7} {4, 5} := by
  constructor
  · intro b hb
    simp at hb
    subst b
    omega
  constructor
  · intro c hc
    simp at hc
    rcases hc with rfl | rfl <;> omega
  · simp [AvoidsDistinctSums]

end Submissions.Erdos788ConcreteIntervals.Direct
