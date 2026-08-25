import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos1059FactorialAvoidingPrimes

def IsFactorial (d : ℕ) : Prop :=
  d ∈ Set.range Nat.factorial

def factorialsBelow (n : ℕ) : Set ℕ :=
  {d | d < n ∧ IsFactorial d}

def IsComposite (n : ℕ) : Prop :=
  1 < n ∧ ¬n.Prime

def AvoidsPrimeFactorialDifferences (n : ℕ) : Prop :=
  ∀ d ∈ factorialsBelow n, IsComposite (n - d)

/-- Erdős Problem 1059: infinitely many primes have composite
difference from every positive factorial below them. -/
abbrev statement : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ AvoidsPrimeFactorialDifferences p}

theorem target : statement := sorry

end Statements.Erdos1059FactorialAvoidingPrimes
