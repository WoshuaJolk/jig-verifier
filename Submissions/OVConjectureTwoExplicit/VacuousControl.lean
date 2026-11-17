import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.OVConjectureTwoExplicit.VacuousControl

/-- Must-fail control: drops the conclusion of the statement. It is true and
compiles, and must be refused as a restatement. -/
theorem proof : ∀ (p k : ℕ), p.Prime → 2 ≤ k → True := by
  intro _ _ _ _
  trivial

end Submissions.OVConjectureTwoExplicit.VacuousControl
