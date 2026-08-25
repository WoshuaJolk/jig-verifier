import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos730ExplicitPrimeSupportPairs

abbrev S : Set (ℕ × ℕ) :=
  {(n, m) : ℕ × ℕ | n < m ∧
    n.centralBinom.primeFactors = m.centralBinom.primeFactors}

/-- Two exact pairs of indices whose central binomial coefficients have the same prime support. -/
abbrev statement : Prop :=
  ({(87, 88), (607, 608)} : Set (ℕ × ℕ)) ⊆ S

theorem target : statement := sorry

end Statements.Erdos730ExplicitPrimeSupportPairs
