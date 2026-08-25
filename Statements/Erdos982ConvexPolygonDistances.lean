import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.LinearAlgebra.Orientation

open scoped EuclideanGeometry Real

namespace Statements.Erdos982ConvexPolygonDistances

scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

noncomputable local instance : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨(PiLp.basisFun 2 ℝ (Fin 2)).orientation⟩

local instance : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Exact inlining of `EuclideanGeometry.IsCcwConvexPolygon` from FormalConjecturesForMathlib: every increasing triple has positive oriented angle. -/
def IsCcwConvexPolygon {n : ℕ} (p : Fin n → ℝ²) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k →
    (∡ (p i) (p j) (p k)).sign = 1

/-- Exact inlining of `EuclideanGeometry.IsConvexPolygon`: either the supplied cyclic order or its reversal is counter-clockwise convex. -/
def IsConvexPolygon {n : ℕ} (p : Fin n → ℝ²) : Prop :=
  IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i ↦ p (-i)

/-- Erdős Problem 982, with the non-Mathlib convex-polygon helper inlined. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ∀ p : Fin n → ℝ², Function.Injective p →
      IsConvexPolygon p →
        ∃ i : Fin n,
          {d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j)}.ncard ≥ n / 2

theorem target : statement := sorry

end Statements.Erdos982ConvexPolygonDistances
