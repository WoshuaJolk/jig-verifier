import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Interval.Finset.Fin

namespace Statements.Erdos306SemiprimeEgyptianFractions

open ArithmeticFunction
open scoped omega Omega BigOperators

/-- Erdős problem 306: every positive rational with squarefree reduced
denominator is a finite sum of distinct reciprocals of products of two
distinct primes. -/
abbrev statement : Prop :=
  ∀ q : ℚ, 0 < q → Squarefree q.den →
    ∃ k : ℕ, ∃ n : Fin (k + 1) → ℕ,
      n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / n i

theorem target : statement := sorry

end Statements.Erdos306SemiprimeEgyptianFractions
