import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

namespace Submissions.Erdos1083SingletonBoundary.Simp

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def distanceCount {d : ℕ} (P : Finset (Space d)) : ℕ :=
  (((P ×ˢ P).filter fun q => q.1 ≠ q.2).image fun q => dist q.1 q.2).card

theorem proof :
    ∀ (d : ℕ) (p : Space d), distanceCount {p} = 0 := by
  intro d p
  simp [distanceCount]

end Submissions.Erdos1083SingletonBoundary.Simp
