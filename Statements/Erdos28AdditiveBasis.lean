import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Order.LiminfLimsup

open Filter Set
open scoped Pointwise

namespace Statements.Erdos28AdditiveBasis

/-- The ordered number of representations of `n` as a sum of two elements of `A`. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A).card

/-- Erdős Problem 28, the Erdős--Turán conjecture on asymptotic additive bases. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, (A + A)ᶜ.Finite →
    limsup (fun n : ℕ => (representationCount A n : ℕ∞)) atTop = (⊤ : ℕ∞)

theorem target : statement := sorry

end Statements.Erdos28AdditiveBasis
