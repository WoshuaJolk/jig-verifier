import Mathlib.Analysis.Complex.Basic

namespace Submissions.Erdos104ThreePointUnitCircle.Degenerate

noncomputable def richCenters (P : Finset ℂ) : Set ℂ :=
  {c : ℂ | 3 ≤ (P.filter fun p => dist p c = 1).card}

/-- Must-fail control: adds an impossible hypothesis. -/
theorem proof :
    False →
      (0 : ℂ) ∈ richCenters (insert Complex.I (insert (-1) {1})) :=
  False.elim

end Submissions.Erdos104ThreePointUnitCircle.Degenerate
