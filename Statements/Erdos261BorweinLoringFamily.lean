import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

open scoped BigOperators
open Finset

namespace Statements.Erdos261BorweinLoringFamily

def indices (n m : ℕ) : Finset ℕ :=
  (range m).image fun i => n + i + 1

def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

/-- The Borwein--Loring telescoping family of exact representations. -/
abbrev statement : Prop :=
  ∀ (n m : ℕ), 2 ≤ m →
    n + m + 2 = 2 ^ (m + 1) →
    HasRepresentation n

theorem target : statement := sorry

end Statements.Erdos261BorweinLoringFamily
