import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos291FirstFiveCoprime

def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

/-- The first five positive indices satisfy the coprimality in Erdős 291. -/
abbrev statement : Prop :=
  ∀ n ∈ Finset.Icc 1 5, Nat.gcd (a n) (L n) = 1

theorem target : statement := sorry

end Statements.Erdos291FirstFiveCoprime
