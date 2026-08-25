import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos417TotientValueRatioDiverges

open Filter Set

/-- The number of totient values at most `x`, allowing arbitrary preimages. -/
noncomputable def V (x : ℕ) : ℕ :=
  {k : ℕ | k ∈ Set.range Nat.totient ∧ k ≤ x}.ncard

/-- The number of distinct totient values attained by inputs at most `x`. -/
noncomputable def V' (x : ℕ) : ℕ :=
  (Nat.totient '' Set.Icc 1 x).ncard

/-- The stronger possibility suggested by Erdős in Problem 417: the ratio
`V(x) / V'(x)` tends to infinity. -/
abbrev statement : Prop :=
  Tendsto (fun x : ℕ ↦ (V x : ℝ) / (V' x : ℝ)) atTop atTop

theorem target : statement := sorry

end Statements.Erdos417TotientValueRatioDiverges
