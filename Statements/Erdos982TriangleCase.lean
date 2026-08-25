import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.LinearAlgebra.Orientation

open scoped EuclideanGeometry Real

namespace Statements.Erdos982TriangleCase

scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

noncomputable local instance : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨(PiLp.basisFun 2 ℝ (Fin 2)).orientation⟩

local instance : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

def IsCcwConvexPolygon (p : Fin 3 → ℝ²) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k →
    (∡ (p i) (p j) (p k)).sign = 1

def IsConvexPolygon (p : Fin 3 → ℝ²) : Prop :=
  IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i ↦ p (-i)

/-- The three-vertex boundary of Erdős 982. -/
abbrev statement : Prop :=
  ∀ p : Fin 3 → ℝ², Function.Injective p →
    IsConvexPolygon p →
      ∃ i : Fin 3,
        {d : ℝ | ∃ j : Fin 3, j ≠ i ∧ d = dist (p i) (p j)}.ncard ≥ 3 / 2

theorem target : statement := sorry

end Statements.Erdos982TriangleCase
