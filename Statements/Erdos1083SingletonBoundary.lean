import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

namespace Statements.Erdos1083SingletonBoundary

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def distanceCount {d : ℕ} (P : Finset (Space d)) : ℕ :=
  (((P ×ˢ P).filter fun q => q.1 ≠ q.2).image fun q => dist q.1 q.2).card

abbrev statement : Prop :=
  ∀ (d : ℕ) (p : Space d), distanceCount {p} = 0

theorem target : statement := sorry

end Statements.Erdos1083SingletonBoundary
