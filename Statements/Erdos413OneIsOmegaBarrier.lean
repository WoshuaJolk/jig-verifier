import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos413OneIsOmegaBarrier

def omega (n : ℕ) : ℕ :=
  n.factorization.support.card

def IsBarrier (n : ℕ) : Prop :=
  ∀ m < n, m + omega m ≤ n

/-- One is a barrier for the distinct-prime-factor counting function. -/
abbrev statement : Prop :=
  IsBarrier 1

theorem target : statement := sorry

end Statements.Erdos413OneIsOmegaBarrier
