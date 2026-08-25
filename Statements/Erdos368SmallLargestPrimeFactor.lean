import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Statements.Erdos368SmallLargestPrimeFactor

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- Erdős problem 368: infinitely many unusually smooth consecutive products. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    {n : ℕ | 2 ≤ n ∧
      (maxPrimeFac (n * (n + 1)) : ℝ) <
        (Real.log (n : ℝ)) ^ (2 + ε)}.Infinite

theorem target : statement := sorry

end Statements.Erdos368SmallLargestPrimeFactor
