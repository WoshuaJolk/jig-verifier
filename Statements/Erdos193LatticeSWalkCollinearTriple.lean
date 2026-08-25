import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace Statements.Erdos193LatticeSWalkCollinearTriple

open Set

def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop :=
  ∀ n, a (n + 1) - a n ∈ S

def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V]
    [Module R V] (A : Set V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear R ({x, y, z} : Set V)

/-- Erdős Problem 193: every infinite-range walk in `ℤ³` with finitely many
allowed steps contains three distinct collinear points. -/
abbrev statement : Prop :=
  ∀ S : Set (Fin 3 → ℤ), S.Finite →
    ∀ a : ℕ → Fin 3 → ℤ, IsSWalk S a → (range a).Infinite →
      HasCollinearTriple ℚ
        (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ))

theorem target : statement := sorry

end Statements.Erdos193LatticeSWalkCollinearTriple
