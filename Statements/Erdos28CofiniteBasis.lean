import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Set.Finite.Lattice

open Set

namespace Statements.Erdos28CofiniteBasis

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) => p.1 ∈ A ∧ p.2 ∈ A).card

/-- The Erdős--Turán conclusion in elementary unboundedness form for cofinite bases. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ), Aᶜ.Finite →
    ∀ k : ℕ, ∃ n : ℕ, k ≤ representationCount A n

theorem target : statement := sorry

end Statements.Erdos28CofiniteBasis
