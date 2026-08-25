import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod

open scoped Pointwise

namespace Statements.Erdos52SidonSubsetBridge

/-- A quantitative transfer from Sidon subsets to the ambient sum-product maximum. -/
abbrev statement : Prop :=
  ∀ A B : Finset ℤ, B ⊆ A →
    (∀ a ∈ B, ∀ b ∈ B, a ≤ b →
      ∀ c ∈ B, ∀ d ∈ B, c ≤ d →
        a + b = c + d → a = c ∧ b = d) →
    B.card * (B.card + 1) ≤
      2 * max (A + A).card (A * A).card

theorem target : statement := sorry

end Statements.Erdos52SidonSubsetBridge
