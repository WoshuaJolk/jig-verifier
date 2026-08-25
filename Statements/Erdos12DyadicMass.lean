import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Interval.Finset.Nat

/-!
# Reciprocal-mass control in an anchored dyadic shell

The same reflection that bounds cardinality gives a weighted injection.  Each
selected `b` is charged to the distinct representative `min b (3a-b)` in the
lower half-shell; the representative is no larger than `b`.
-/

namespace Statements.Erdos12DyadicMass

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (B : Finset ℕ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c) →
    ∀ a ∈ A,
      (∀ b ∈ B, b ∈ A ∧ a < b ∧ b < 2 * a) →
      (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
        ∑ n ∈ Finset.Ioc a (a + a / 2), (1 : ℝ) / (n : ℝ)

theorem target : statement := sorry

end Statements.Erdos12DyadicMass
