import Mathlib.Data.Nat.Basic

namespace Statements.Erdos675ZeroBoundary

def IsSumTwoSquares (m : ℕ) : Prop :=
  ∃ x y : ℕ, m = x ^ 2 + y ^ 2

abbrev statement : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧
    ∀ a : ℕ, 1 ≤ a → a ≤ 0 →
      (IsSumTwoSquares a ↔ IsSumTwoSquares (a + t))

theorem target : statement := sorry

end Statements.Erdos675ZeroBoundary
