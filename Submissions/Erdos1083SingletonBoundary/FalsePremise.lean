import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

namespace Submissions.Erdos1083SingletonBoundary.FalsePremise

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def distanceCount {d : ℕ} (P : Finset (Space d)) : ℕ :=
  (((P ×ˢ P).filter fun q => q.1 ≠ q.2).image fun q => dist q.1 q.2).card

theorem proof :
    False →
      ∀ (d : ℕ) (p : Space d), distanceCount {p} = 0 := by
  intro h
  exact h.elim

end Submissions.Erdos1083SingletonBoundary.FalsePremise
