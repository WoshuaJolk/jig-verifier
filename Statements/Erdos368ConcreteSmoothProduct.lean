import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Statements.Erdos368ConcreteSmoothProduct

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- The consecutive product `48*49` satisfies the ε=1 inequality. -/
abbrev statement : Prop :=
  (maxPrimeFac (48 * (48 + 1)) : ℝ) <
    (Real.log (48 : ℝ)) ^ (2 + (1 : ℝ))

theorem target : statement := sorry

end Statements.Erdos368ConcreteSmoothProduct
