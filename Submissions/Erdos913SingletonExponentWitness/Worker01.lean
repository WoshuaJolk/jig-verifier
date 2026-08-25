import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Submissions.Erdos913SingletonExponentWitness.Worker01

def HasDistinctExponents (n : ℕ) : Prop :=
  ∀ p ∈ (n * (n + 1)).primeFactors,
    ∀ q ∈ (n * (n + 1)).primeFactors,
      (n * (n + 1)).factorization p =
        (n * (n + 1)).factorization q → p = q

theorem proof : HasDistinctExponents 1 := by
  norm_num [HasDistinctExponents, Nat.primeFactors, Nat.primeFactorsList]

end Submissions.Erdos913SingletonExponentWitness.Worker01
