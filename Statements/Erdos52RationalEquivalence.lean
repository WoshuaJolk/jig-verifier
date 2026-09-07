import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Pointwise

namespace Statements.Erdos52RationalEquivalence

abbrev statement : Prop :=
    (∀ A : Finset ℚ, ∃ B : Finset ℤ, B.card = A.card ∧
      (B + B).card = (A + A).card ∧ (B * B).card = (A * A).card) ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
        (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)) ↔
     (∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℚ,
        (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)))

theorem target : statement := sorry

end Statements.Erdos52RationalEquivalence
