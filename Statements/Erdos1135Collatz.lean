import Mathlib.Data.Nat.Totient
import Mathlib.Logic.Function.Iterate

namespace Statements.Erdos1135Collatz

def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- The Collatz conjecture in the upstream unaccelerated convention. -/
abbrev statement : Prop :=
  ∀ n : ℕ, n > 0 → ∃ m : ℕ, collatzStep^[m] n = 1

theorem target : statement := sorry

end Statements.Erdos1135Collatz
