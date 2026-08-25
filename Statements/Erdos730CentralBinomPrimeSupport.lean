import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos730CentralBinomPrimeSupport

abbrev S : Set (ℕ × ℕ) :=
  {(n, m) : ℕ × ℕ | n < m ∧
    n.centralBinom.primeFactors = m.centralBinom.primeFactors}

/-- Erdős Problem 730: infinitely many distinct central binomial coefficients have identical prime support in pairs. -/
abbrev statement : Prop :=
  S.Infinite

theorem target : statement := sorry

end Statements.Erdos730CentralBinomPrimeSupport
