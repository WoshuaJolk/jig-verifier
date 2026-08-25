import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos913DistinctFactorizationExponents

def HasDistinctExponents (n : ℕ) : Prop :=
  ∀ p ∈ (n * (n + 1)).primeFactors,
    ∀ q ∈ (n * (n + 1)).primeFactors,
      (n * (n + 1)).factorization p =
        (n * (n + 1)).factorization q → p = q

/-- Erdős Problem 913: infinitely many products of two consecutive integers
have pairwise distinct positive prime-factor exponents. -/
abbrev statement : Prop :=
  {n : ℕ | HasDistinctExponents n}.Infinite

theorem target : statement := sorry

end Statements.Erdos913DistinctFactorizationExponents
