import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

open scoped BigOperators

namespace Statements.Erdos931ConsecutiveBlockPrimeSupports

/-- Erdős Problem 931: for fixed block lengths `k₁ ≥ k₂ ≥ 3`, only
finitely many separated pairs of starting points should yield consecutive
products with exactly the same prime support. -/
abbrev statement : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    {pair : ℕ × ℕ |
      pair.1 + k₁ ≤ pair.2 ∧
      (Finset.prod (Finset.Icc 1 k₁) (fun i => pair.1 + i)).primeFactors =
        (Finset.prod (Finset.Icc 1 k₂) (fun j => pair.2 + j)).primeFactors}.Finite

theorem target : statement := sorry

end Statements.Erdos931ConsecutiveBlockPrimeSupports
