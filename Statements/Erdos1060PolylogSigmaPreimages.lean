import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Asymptotics Finset Filter Real
open scoped ArithmeticFunction.sigma

namespace Statements.Erdos1060PolylogSigmaPreimages

def solutionCount (n : ℕ) : ℕ :=
  #{k ≤ n | k * σ 1 k = n}

/-- Part (ii), the stronger proposed bound in Erdős Problem 1060. -/
abbrev statement : Prop :=
  ∃ C : ℝ,
    (fun n : ℕ => (solutionCount n : ℝ)) =O[atTop]
      (fun n : ℕ => log n ^ C)

theorem target : statement := sorry

end Statements.Erdos1060PolylogSigmaPreimages
