import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace Statements.Erdos173ConstantColoring

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Triangle := Fin 3 → Point

def Congruent (T U : Triangle) : Prop :=
  ∃ permutation : Equiv.Perm (Fin 3),
    ∀ i j, dist (T i) (T j) =
      dist (U (permutation i)) (U (permutation j))

def HasMonochromaticCopy (color : Point → Fin 2) (T : Triangle) : Prop :=
  ∃ U : Triangle, Congruent T U ∧
    ∃ c : Fin 2, ∀ i, color (U i) = c

/-- Every triangle is monochromatic under a constant plane colouring. -/
abbrev statement : Prop :=
  ∀ c : Fin 2, ∀ T : Triangle,
    HasMonochromaticCopy (fun _ => c) T

theorem target : statement := sorry

end Statements.Erdos173ConstantColoring
