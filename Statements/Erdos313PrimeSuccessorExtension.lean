import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs

namespace Statements.Erdos313PrimeSuccessorExtension

open Finset

def IsSolution (m : ℕ) (P : Finset ℕ) : Prop :=
  2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧
    ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m

/-- The classical prime-successor extension for primary pseudoperfect
solutions. -/
abbrev statement : Prop :=
  ∀ m P, IsSolution m P → (m + 1).Prime → m + 1 ∉ P →
    IsSolution (m * (m + 1)) (insert (m + 1) P)

theorem target : statement := sorry

end Statements.Erdos313PrimeSuccessorExtension
