import Mathlib.Data.Nat.Factorization.Basic

open Nat

namespace Statements.Erdos939OnePowerfulBoundary

def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

/-- One is `r`-powerful for every exponent. -/
abbrev statement : Prop :=
  ∀ r : ℕ, IsFull r 1

theorem target : statement := sorry

end Statements.Erdos939OnePowerfulBoundary
