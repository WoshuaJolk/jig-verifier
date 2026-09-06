import Mathlib.NumberTheory.FactorisationProperties

namespace Statements.Erdos470ThreePrimeFactors

/-- Every odd weird number has at least three distinct prime factors. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Odd n → n.Weird → 3 ≤ n.primeFactors.card

theorem target : statement := sorry

end Statements.Erdos470ThreePrimeFactors
