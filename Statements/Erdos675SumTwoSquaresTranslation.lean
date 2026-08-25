import Mathlib.Data.Nat.Basic

/-!
# Erdős problem 675

Does the set of positive integers representable as a sum of two squares have
the translation property?  Here the translation property means that every
finite initial membership pattern reappears after a positive translation.
-/

namespace Statements.Erdos675SumTwoSquaresTranslation

def IsSumTwoSquares (m : ℕ) : Prop :=
  ∃ x y : ℕ, m = x ^ 2 + y ^ 2

def HasTranslationProperty (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, 1 ≤ t ∧
    ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

abbrev statement : Prop :=
  HasTranslationProperty {m : ℕ | IsSumTwoSquares m}

theorem target : statement := sorry

end Statements.Erdos675SumTwoSquaresTranslation
