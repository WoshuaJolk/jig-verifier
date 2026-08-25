import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos850ThreeConsecutivePrimeSupports

/-- Erdős Problem 850: two distinct starts have equal prime support at each of three consecutive offsets. -/
abbrev statement : Prop :=
  ∃ x y : ℕ, x ≠ y ∧
    x.primeFactors = y.primeFactors ∧
    (x + 1).primeFactors = (y + 1).primeFactors ∧
    (x + 2).primeFactors = (y + 2).primeFactors

theorem target : statement := sorry

end Statements.Erdos850ThreeConsecutivePrimeSupports
