import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos431InverseGoldbach

def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

/-- Ostmann's inverse Goldbach conjecture: the primes are not, up to
finitely many exceptions, the sumset of two infinite sets of positive
integers. -/
abbrev statement : Prop :=
  ¬ ∃ A B : Set ℕ,
    0 ∉ A ∧ 0 ∉ B ∧ A.Infinite ∧ B.Infinite ∧
      {n : ℕ | (n ∈ sumset A B) ≠ n.Prime}.Finite

theorem target : statement := sorry

end Statements.Erdos431InverseGoldbach
