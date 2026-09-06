import Mathlib.NumberTheory.FactorisationProperties

namespace Statements.Erdos470SevenPrimesIfNotThree

/-- Every odd weird number not divisible by 3 has at least seven distinct prime factors. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Odd n → ¬ 3 ∣ n → n.Weird → 7 ≤ n.primeFactors.card

theorem target : statement := sorry

end Statements.Erdos470SevenPrimesIfNotThree
