import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos137ThreeBlockResidue36

open Finset
open scoped BigOperators

def Powerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

def consecutiveProduct (start length : ℕ) : ℕ :=
  ∏ x ∈ Finset.Ioc start (start + length), x

/-- Necessary residue condition for Erdős problem 137 at block length three:
if the product (s+1)(s+2)(s+3) of three consecutive positive integers is
powerful, then s+1 is confined to nine of the thirty-six residues modulo 36. -/
abbrev statement : Prop :=
  ∀ s : ℕ, Powerful (consecutiveProduct s 3) →
    (s + 1) % 36 = 0 ∨ (s + 1) % 36 = 7 ∨ (s + 1) % 36 = 8 ∨
    (s + 1) % 36 = 16 ∨ (s + 1) % 36 = 18 ∨ (s + 1) % 36 = 26 ∨
    (s + 1) % 36 = 27 ∨ (s + 1) % 36 = 34 ∨ (s + 1) % 36 = 35

theorem target : statement := sorry

end Statements.Erdos137ThreeBlockResidue36
