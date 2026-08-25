import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos68PrimitiveNonCancellation

/-- A prime that first appears in `N! - 1` cannot cancel from the canonical
common numerator of the finite reciprocal sum from `2` through `N`. -/
abbrev statement : Prop :=
  ∀ N p : ℕ, 2 ≤ N → p.Prime → p ∣ N.factorial - 1 →
    (∀ n : ℕ, 2 ≤ n → n < N → ¬p ∣ n.factorial - 1) →
    ¬p ∣
      ∑ n ∈ Finset.Icc 2 N,
        ∏ m ∈ (Finset.Icc 2 N).erase n, (m.factorial - 1)

theorem target : statement := sorry

end Statements.Erdos68PrimitiveNonCancellation
