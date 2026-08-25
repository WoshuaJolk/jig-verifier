import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos68UniqueMaxValuation

/-- If one factorial-minus-one denominator in a finite truncation has strictly
largest `p`-adic valuation, its reciprocal has uniquely smallest valuation and
therefore determines the valuation of the whole finite sum. -/
abbrev statement : Prop :=
  ∀ N k p : ℕ, 2 ≤ k → k ≤ N → p.Prime →
    (∀ n ∈ Finset.Icc 2 N, n ≠ k →
      padicValNat p (n.factorial - 1) <
        padicValNat p (k.factorial - 1)) →
    padicValRat p
        (∑ n ∈ Finset.Icc 2 N,
          (1 : ℚ) / (n.factorial - 1 : ℕ)) =
      -(padicValNat p (k.factorial - 1) : ℤ)

theorem target : statement := sorry

end Statements.Erdos68UniqueMaxValuation
