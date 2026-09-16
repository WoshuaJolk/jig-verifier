import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Defs

namespace Statements.J5P184CyclicPrimeBound

/-- Finite prime-parameter lower bound; all displayed arithmetic is in integers. -/
abbrev statement : Prop :=
  ∀ (A : Finset ℝ) (p : ℕ), p.Prime →
    ∃ S : Finset ℝ, S ⊆ A ∧
      (∀ ⦃a b c d : ℝ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      4 * (p : ℤ) * ((p : ℤ) - 1) * A.card -
          (A.card : ℤ) * ((A.card : ℤ) - 1) ≤
        8 * (p : ℤ) ^ 2 * ((p : ℤ) - 1) * S.card

end Statements.J5P184CyclicPrimeBound
