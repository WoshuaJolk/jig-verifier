import Mathlib.Analysis.InnerProductSpace.EuclideanDist

namespace Submissions.Erdos173ConstantColoring.Direct

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Triangle := Fin 3 → Point

def Congruent (T U : Triangle) : Prop :=
  ∃ permutation : Equiv.Perm (Fin 3),
    ∀ i j, dist (T i) (T j) =
      dist (U (permutation i)) (U (permutation j))

def HasMonochromaticCopy (color : Point → Fin 2) (T : Triangle) : Prop :=
  ∃ U : Triangle, Congruent T U ∧
    ∃ c : Fin 2, ∀ i, color (U i) = c

theorem proof :
    ∀ c : Fin 2, ∀ T : Triangle,
      HasMonochromaticCopy (fun _ => c) T := by
  intro c T
  refine ⟨T, ⟨Equiv.refl _, ?_⟩, c, ?_⟩
  · simp
  · simp

end Submissions.Erdos173ConstantColoring.Direct
