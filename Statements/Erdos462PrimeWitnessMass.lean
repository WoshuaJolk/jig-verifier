import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos462PrimeWitnessMass

open Finset

/-- Any interval containing a prime already carries least-prime-factor
weight at least one. -/
abbrev statement : Prop :=
  ∀ a b p : ℕ, p.Prime → p ∈ Icc a b →
    1 ≤ ∑ n ∈ Icc a b, (n.minFac : ℝ) / n

theorem target : statement := sorry

end Statements.Erdos462PrimeWitnessMass
