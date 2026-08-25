import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos366SquarefullThenCubefull

/-- `n` is `k`-full when every prime divisor occurs to exponent at least
`k`. -/
def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- Erdős problem 366: does a positive square-full integer ever have a
cube-full successor? -/
abbrev statement : Prop :=
  ∃ n > 0, Full 2 n ∧ Full 3 (n + 1)

theorem target : statement := sorry

end Statements.Erdos366SquarefullThenCubefull
