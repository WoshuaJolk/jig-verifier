import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos137ElementwisePowerfulBlock

open Finset
open scoped BigOperators

def Powerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

def consecutiveProduct (start length : ℕ) : ℕ :=
  ∏ x ∈ Finset.Ioc start (start + length), x

/-- A sufficient condition for a block product to be powerful: if every element
of the block is powerful, so is the product. No coprimality is needed. -/
abbrev statement : Prop :=
  ∀ start length : ℕ,
    (∀ x ∈ Finset.Ioc start (start + length), Powerful x) →
      Powerful (consecutiveProduct start length)

theorem target : statement := sorry

end Statements.Erdos137ElementwisePowerfulBlock
