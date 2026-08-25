import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.Asymptotics.Defs

namespace Statements.Erdos104UnitCircleSubquadratic

open Filter Asymptotics

/-- Centers of unit circles containing at least three points of `P`. -/
noncomputable def richCenters (P : Finset ℂ) : Set ℂ :=
  {c : ℂ | 3 ≤ (P.filter fun p => dist p c = 1).card}

/-- The maximum number of distinct 3-rich unit circles determined by `n` points. -/
noncomputable def maxRichUnitCircles (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset ℂ,
    P.card = n ∧ (richCenters P).ncard = k}

/-- Erdős problem 104: 3-rich unit circles are subquadratic in the point count. -/
abbrev statement : Prop :=
  (fun n => (maxRichUnitCircles n : ℝ)) =o[atTop]
    (fun n => (n : ℝ) ^ 2)

theorem target : statement := sorry

end Statements.Erdos104UnitCircleSubquadratic
