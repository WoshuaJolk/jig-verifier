import Mathlib

open Filter

namespace Statements.Erdos1005FareyQuarter

/-- A rational is in the Farey sequence of order `n`. -/
def IsFarey (n : ℕ) (q : ℚ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n

/-- The number of order-`n` Farey fractions strictly between `x` and `y`. -/
noncomputable def betweenCount (n : ℕ) (x y : ℚ) : ℕ :=
  {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.ncard

/-- A pair of Farey fractions is badly ordered when its numerators increase while
its denominators decrease. -/
def BadlyOrdered (n : ℕ) (x y : ℚ) : Prop :=
  IsFarey n x ∧ IsFarey n y ∧ x < y ∧ x.num < y.num ∧ y.den < x.den

/-- The minimum number of intervening Farey fractions among badly ordered pairs. -/
noncomputable def fVal (n : ℕ) : ℕ :=
  sInf {k | ∃ x y, BadlyOrdered n x y ∧ betweenCount n x y = k}

/-- Erdős Problem 1005: the badly ordered Farey interval has asymptotic constant `1/4`. -/
abbrev statement : Prop :=
  Tendsto (fun n : ℕ => (fVal n : ℝ) / n) atTop (nhds (1 / 4))

theorem target : statement := sorry

end Statements.Erdos1005FareyQuarter
