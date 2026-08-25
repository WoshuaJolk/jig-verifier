import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos203FiniteBoxWitness

/-- The explicit candidate `427771` avoids primes throughout the complete
`0 ≤ k,l ≤ 8` exponent box. -/
abbrev statement : Prop :=
  Nat.Coprime 427771 6 ∧
    ∀ k ≤ 8, ∀ l ≤ 8,
      ¬(2 ^ k * 3 ^ l * 427771 + 1).Prime

theorem target : statement := sorry

end Statements.Erdos203FiniteBoxWitness
