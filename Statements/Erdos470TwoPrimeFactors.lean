import Mathlib.NumberTheory.FactorisationProperties

namespace Statements.Erdos470TwoPrimeFactors

/-- Every odd weird number has at least two distinct prime factors. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Odd n → n.Weird → 2 ≤ n.primeFactors.card

theorem target : statement := sorry

end Statements.Erdos470TwoPrimeFactors
