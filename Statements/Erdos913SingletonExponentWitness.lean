import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos913SingletonExponentWitness

def HasDistinctExponents (n : ℕ) : Prop :=
  ∀ p ∈ (n * (n + 1)).primeFactors,
    ∀ q ∈ (n * (n + 1)).primeFactors,
      (n * (n + 1)).factorization p =
        (n * (n + 1)).factorization q → p = q

/-- The smallest positive instance has only the prime factor `2`, hence its
factorization exponents are vacuously pairwise distinct. -/
abbrev statement : Prop :=
  HasDistinctExponents 1

theorem target : statement := sorry

end Statements.Erdos913SingletonExponentWitness
