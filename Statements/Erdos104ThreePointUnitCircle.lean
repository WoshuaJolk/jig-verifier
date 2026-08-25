import Mathlib.Analysis.Complex.Basic

namespace Statements.Erdos104ThreePointUnitCircle

noncomputable def richCenters (P : Finset ℂ) : Set ℂ :=
  {c : ℂ | 3 ≤ (P.filter fun p => dist p c = 1).card}

/-- The unit circle centered at zero contains `1`, `-1`, and `i`. -/
abbrev statement : Prop :=
  (0 : ℂ) ∈ richCenters (insert Complex.I (insert (-1) {1}))

theorem target : statement := sorry

end Statements.Erdos104ThreePointUnitCircle
