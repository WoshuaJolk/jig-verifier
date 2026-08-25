import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Published counterexample to Erdős Problem 193

The terminal-steered Hilbert construction supplies a finite step set and an
infinite-range walk in `ℤ³` with no three distinct collinear vertices.
-/

namespace Statements.Erdos193HilbertCounterexample

open Set

def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop :=
  ∀ n, a (n + 1) - a n ∈ S

def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V]
    [Module R V] (A : Set V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear R ({x, y, z} : Set V)

/-- The exact negation of the canonical Erdős 193 root. -/
abbrev statement : Prop :=
  ¬ (∀ S : Set (Fin 3 → ℤ), S.Finite →
    ∀ a : ℕ → Fin 3 → ℤ, IsSWalk S a → (range a).Infinite →
      HasCollinearTriple ℚ
        (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ)))

theorem target : statement := sorry

end Statements.Erdos193HilbertCounterexample
