import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs

namespace Statements.Erdos313PrimaryPseudoperfectInfinite

open Finset

def solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧
    ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

/-- Erdős Problem 313: there are infinitely many primary pseudoperfect
solutions. -/
abbrev statement : Prop :=
  solutions.Infinite

theorem target : statement := sorry

end Statements.Erdos313PrimaryPseudoperfectInfinite
