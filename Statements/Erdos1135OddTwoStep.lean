import Mathlib.Data.Nat.Totient

namespace Statements.Erdos1135OddTwoStep

def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- Every odd input `2n+1` reaches the accelerated odd Collatz value
`3n+2` after exactly two unaccelerated steps. -/
abbrev statement : Prop :=
  ∀ n : ℕ, collatzStep (collatzStep (2 * n + 1)) = 3 * n + 2

theorem target : statement := sorry

end Statements.Erdos1135OddTwoStep
