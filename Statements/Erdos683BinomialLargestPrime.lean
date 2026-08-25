import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos683BinomialLargestPrime

def largestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- Erdős 683: a binomial coefficient always has a prime factor
polynomially larger than the shorter nontrivial side of its parameters. -/
abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    min ((n - k + 1 : ℕ) : ℝ) ((k : ℝ) ^ (1 + c)) ≤
      (largestPrimeFactor (n.choose k) : ℝ)

theorem target : statement := sorry

end Statements.Erdos683BinomialLargestPrime
