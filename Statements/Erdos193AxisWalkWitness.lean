import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace Statements.Erdos193AxisWalkWitness

open Set

def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop :=
  ∀ n, a (n + 1) - a n ∈ S

def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V]
    [Module R V] (A : Set V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear R ({x, y, z} : Set V)

def axisStep : Fin 3 → ℤ := fun i ↦ if i = 0 then 1 else 0

def axisWalk : ℕ → Fin 3 → ℤ := fun n ↦ (n : ℤ) • axisStep

/-- A concrete nondegenerate instance exercises the walk, infinite-range,
integer-to-rational embedding, and collinearity definitions. -/
abbrev statement : Prop :=
  IsSWalk {axisStep} axisWalk ∧ (range axisWalk).Infinite ∧
    HasCollinearTriple ℚ
      (range (fun n ↦ (↑) ∘ axisWalk n : ℕ → Fin 3 → ℚ))

theorem target : statement := sorry

end Statements.Erdos193AxisWalkWitness
