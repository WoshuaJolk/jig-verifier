import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Lattice

namespace Statements.Erdos431ParityStructure

def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

/-- In any hypothetical asymptotic decomposition of the primes, each
summand set must occupy a single parity class. -/
abbrev statement : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite →
    {n : ℕ | (n ∈ sumset A B) ≠ n.Prime}.Finite →
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ % 2 = a₂ % 2) ∧
      (∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ % 2 = b₂ % 2)

theorem target : statement := sorry

end Statements.Erdos431ParityStructure
