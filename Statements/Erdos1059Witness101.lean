import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos1059Witness101

def IsFactorial (d : ℕ) : Prop := d ∈ Set.range Nat.factorial
def factorialsBelow (n : ℕ) : Set ℕ := {d | d < n ∧ IsFactorial d}
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime
def AvoidsPrimeFactorialDifferences (n : ℕ) : Prop :=
  ∀ d ∈ factorialsBelow n, IsComposite (n - d)

/-- The first published example for Erdős 1059. -/
abbrev statement : Prop :=
  Nat.Prime 101 ∧ AvoidsPrimeFactorialDifferences 101

theorem target : statement := sorry

end Statements.Erdos1059Witness101
