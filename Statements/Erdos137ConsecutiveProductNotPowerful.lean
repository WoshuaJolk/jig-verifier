import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos137ConsecutiveProductNotPowerful

open Finset
open scoped BigOperators

def Powerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

def consecutiveProduct (start length : ℕ) : ℕ :=
  ∏ x ∈ Finset.Ioc start (start + length), x

/-- Erdős Problem 137: no product of three or more consecutive positive
integers is powerful. -/
abbrev statement : Prop :=
  ∀ length : ℕ, 3 ≤ length →
    ∀ start : ℕ, ¬Powerful (consecutiveProduct start length)

theorem target : statement := sorry

end Statements.Erdos137ConsecutiveProductNotPowerful
