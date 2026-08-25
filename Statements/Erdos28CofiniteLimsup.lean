import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Order.LiminfLimsup

open Filter Set
open scoped Pointwise

namespace Statements.Erdos28CofiniteLimsup

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A).card

/-- The Erdős--Turán conclusion, in the root's limsup formulation, for cofinite sets. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, Aᶜ.Finite →
    limsup (fun n : ℕ => (representationCount A n : ℕ∞)) atTop = (⊤ : ℕ∞)

theorem target : statement := sorry

end Statements.Erdos28CofiniteLimsup
