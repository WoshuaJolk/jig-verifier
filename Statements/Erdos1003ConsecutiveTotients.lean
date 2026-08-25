import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos1003ConsecutiveTotients

/-- Erdős Problem 1003: Euler's totient should take equal values at
infinitely many consecutive pairs. -/
abbrev statement : Prop :=
  Set.Infinite {n : ℕ | Nat.totient n = Nat.totient (n + 1)}

theorem target : statement := sorry

end Statements.Erdos1003ConsecutiveTotients
