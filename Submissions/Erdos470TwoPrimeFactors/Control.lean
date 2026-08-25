import Mathlib.NumberTheory.FactorisationProperties

namespace Submissions.Erdos470TwoPrimeFactors.Control

abbrev claimedStatement : Prop :=
  ∀ n : ℕ, Odd n → n.Weird → 2 ≤ n.primeFactors.card

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos470TwoPrimeFactors.Control
