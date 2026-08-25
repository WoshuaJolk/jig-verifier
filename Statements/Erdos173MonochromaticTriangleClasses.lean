import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.Independent

namespace Statements.Erdos173MonochromaticTriangleClasses

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Triangle := Fin 3 → Point

def IsTriangle (T : Triangle) : Prop :=
  AffineIndependent ℝ T

def Congruent (T U : Triangle) : Prop :=
  ∃ permutation : Equiv.Perm (Fin 3),
    ∀ i j, dist (T i) (T j) =
      dist (U (permutation i)) (U (permutation j))

def HasMonochromaticCopy (color : Point → Fin 2) (T : Triangle) : Prop :=
  ∃ U : Triangle, Congruent T U ∧
    ∃ c : Fin 2, ∀ i, color (U i) = c

/-- Erdős Problem 173: in every two-colouring of the Euclidean plane,
at most one congruence class of nondegenerate triangles has no
monochromatic copy. -/
abbrev statement : Prop :=
  ∀ color : Point → Fin 2, ∀ T U : Triangle,
    IsTriangle T → IsTriangle U → ¬Congruent T U →
      HasMonochromaticCopy color T ∨ HasMonochromaticCopy color U

theorem target : statement := sorry

end Statements.Erdos173MonochromaticTriangleClasses
