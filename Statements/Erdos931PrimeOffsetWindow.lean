import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos931PrimeOffsetWindow

open scoped BigOperators

def blockProduct (n k : ℕ) : ℕ :=
  Finset.prod (Finset.Icc 1 k) (fun i => n + i)

/-- A prime in the common support of two consecutive-block products
divides one of the finitely many offsets between their terms. -/
abbrev statement : Prop :=
  ∀ k₁ k₂ n₁ n₂ p : ℕ, p.Prime →
    (blockProduct n₁ k₁).primeFactors =
      (blockProduct n₂ k₂).primeFactors →
    p ∈ (blockProduct n₁ k₁).primeFactors →
    ∃ i ∈ Finset.Icc 1 k₁, ∃ j ∈ Finset.Icc 1 k₂,
      (p : ℤ) ∣ (n₂ : ℤ) - n₁ + j - i

theorem target : statement := sorry

end Statements.Erdos931PrimeOffsetWindow
