import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Tactic

open scoped EuclideanGeometry Real

namespace Submissions.Erdos982TriangleCase.Injective

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

theorem proof :
    ∀ p : Fin 3 → ℝ², Function.Injective p →
      IsConvexPolygon p →
        ∃ i : Fin 3,
          {d : ℝ | ∃ j : Fin 3, j ≠ i ∧
            d = dist (p i) (p j)}.ncard ≥ 3 / 2 := by
  intro p hp _hpconv
  let S : Set ℝ :=
    {d : ℝ | ∃ j : Fin 3, j ≠ (0 : Fin 3) ∧
      d = dist (p 0) (p j)}
  have hSfin : S.Finite := by
    apply (Set.finite_range fun j : Fin 3 => dist (p 0) (p j)).subset
    intro d hd
    rcases hd with ⟨j, _hji, rfl⟩
    exact ⟨j, rfl⟩
  have hSnonempty : S.Nonempty := by
    refine ⟨dist (p 0) (p 1), 1, ?_, rfl⟩
    norm_num
  refine ⟨0, ?_⟩
  change S.ncard ≥ 3 / 2
  norm_num
  exact (Set.ncard_pos hSfin).2 hSnonempty

end Submissions.Erdos982TriangleCase.Injective
