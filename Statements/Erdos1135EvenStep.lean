import Mathlib.Data.Nat.Totient

namespace Statements.Erdos1135EvenStep

def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- Every doubled natural takes one Collatz step to its half. -/
abbrev statement : Prop :=
  ∀ n : ℕ, collatzStep (2 * n) = n

theorem target : statement := sorry

end Statements.Erdos1135EvenStep
