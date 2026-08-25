import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Interval.Finset.Fin

namespace Statements.Erdos306SemiprimeUnitFractions

open ArithmeticFunction
open scoped omega Omega BigOperators

/-- Every reciprocal of a product of two distinct primes is a one-term
instance of the semiprime Egyptian-fraction conclusion. -/
abbrev statement : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    ∃ k : ℕ, ∃ n : Fin (k + 1) → ℕ,
      n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      (1 : ℚ) / (p * q) =
        ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / n i

theorem target : statement := sorry

end Statements.Erdos306SemiprimeUnitFractions
