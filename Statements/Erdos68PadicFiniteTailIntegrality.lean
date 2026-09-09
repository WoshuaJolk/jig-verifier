import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos68PadicFiniteTailIntegrality

/-- After a last occurrence of `p` in the sequence `n! - 1`, every finite
sum of later reciprocal terms is a `p`-integral rational. -/
abbrev statement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ K M : ℕ,
    2 ≤ K → K < M →
    (∀ m : ℕ, K < m → ¬p ∣ m.factorial - 1) →
    0 ≤ padicValRat p
      (∑ n ∈ Finset.Icc (K + 1) M,
        (1 : ℚ) / (n.factorial - 1 : ℕ))

theorem target : statement := sorry

end Statements.Erdos68PadicFiniteTailIntegrality
