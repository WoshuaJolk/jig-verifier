import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

namespace Statements.Erdos653LocalSpectrumUpper

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def localCount (X : Finset Point) (p : Point) : ℕ :=
  (X.image fun x => dist x p).card

/-- A configuration has no more distinct local-distance counts than points. -/
abbrev statement : Prop :=
  ∀ X : Finset Point, (X.image (localCount X)).card ≤ X.card

theorem target : statement := sorry

end Statements.Erdos653LocalSpectrumUpper
