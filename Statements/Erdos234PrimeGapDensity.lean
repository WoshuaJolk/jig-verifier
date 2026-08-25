import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos234PrimeGapDensity

open Filter Real Set
open scoped NNReal Topology

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

noncomputable abbrev partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  (S ∩ Set.Iio b).ncard / (Set.Iio b).ncard

def HasDensity (S : Set ℕ) (α : ℝ) : Prop :=
  Tendsto (fun b : ℕ => partialDensity S b) atTop (𝓝 α)

/-- Erdős problem 234: all threshold distributions of normalized consecutive
prime gaps exist, with density continuous in the threshold. -/
abbrev statement : Prop :=
  ∃ f : ℝ≥0 → ℝ, Continuous f ∧
    ∀ c : ℝ≥0,
      HasDensity {n : ℕ | (primeGap n : ℝ) / Real.log n < c} (f c)

theorem target : statement := sorry

end Statements.Erdos234PrimeGapDensity
