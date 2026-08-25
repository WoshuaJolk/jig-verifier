import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos374FactorialSquareWitness527

def IsSquare (n : ℕ) : Prop := ∃ q : ℕ, n = q ^ 2

/-- The six distinct factorial indices from the first known `D₆`
candidate `527 = 17 * 31` have square product. -/
abbrev statement : Prop :=
  IsSquare (Nat.factorial 527 * Nat.factorial 526 *
    Nat.factorial 31 * Nat.factorial 30 *
    Nat.factorial 17 * Nat.factorial 16)

theorem target : statement := sorry

end Statements.Erdos374FactorialSquareWitness527
