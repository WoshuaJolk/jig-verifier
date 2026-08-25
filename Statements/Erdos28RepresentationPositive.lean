import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.Finset.NatAntidiagonal

open Set
open scoped Pointwise

namespace Statements.Erdos28RepresentationPositive

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A).card

/-- Positivity of the representation count is exactly membership in the two-fold sumset. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ) (n : ℕ), 0 < representationCount A n ↔ n ∈ A + A

theorem target : statement := sorry

end Statements.Erdos28RepresentationPositive
