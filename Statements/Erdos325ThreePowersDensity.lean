import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos325ThreePowersDensity

open Asymptotics Filter

def IsSumThreePower (k n : ℕ) : Prop :=
  ∃ a b c, a ^ k + b ^ k + c ^ k = n

noncomputable def countBelow (k x : ℕ) : ℕ :=
  {n ∈ Set.Iic x | IsSumThreePower k n}.ncard

/-- Erdős Problem 325: the expected-order lower bound for integers
representable by three nonnegative `k`th powers. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    (fun x : ℕ ↦ (x : ℝ) ^ (3 / k : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (countBelow k x : ℝ))

theorem target : statement := sorry

end Statements.Erdos325ThreePowersDensity
