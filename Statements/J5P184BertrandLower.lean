import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card

namespace Statements.J5P184BertrandLower

/-- Uniform finite bound; repeated summands are included in the Sidon predicate. -/
abbrev statement : Prop :=
  ∀ (A : Finset ℝ), 10 ≤ A.card →
    ∃ S : Finset ℝ, S ⊆ A ∧
      (∀ ⦃a b c d : ℝ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      6 * Real.sqrt (7 * (A.card : ℝ)) ≤ 49 * (S.card : ℝ) + 64

end Statements.J5P184BertrandLower
