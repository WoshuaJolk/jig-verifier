import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Real

namespace Statements.Erdos1074EHSDensityExists

open Filter
open scoped Nat Topology

def EHSNumbers : Set ℕ :=
  {m | 1 ≤ m ∧
    ∃ p : ℕ, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m.factorial + 1}

noncomputable def partialDensity (n : ℕ) : ℝ :=
  ((EHSNumbers ∩ Set.Iio n).ncard : ℝ) / n

/-- Erdős problem 1074(i): the EHS numbers have a natural density. -/
abbrev statement : Prop :=
  ∃ c : ℝ, Tendsto partialDensity atTop (𝓝 c)

theorem target : statement := sorry

end Statements.Erdos1074EHSDensityExists
