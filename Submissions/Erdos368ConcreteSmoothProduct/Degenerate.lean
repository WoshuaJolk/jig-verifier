import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Submissions.Erdos368ConcreteSmoothProduct.Degenerate

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- Must-fail control: adds an impossible hypothesis. -/
theorem proof :
    False →
      (maxPrimeFac (48 * (48 + 1)) : ℝ) <
        (Real.log (48 : ℝ)) ^ (2 + (1 : ℝ)) :=
  False.elim

end Submissions.Erdos368ConcreteSmoothProduct.Degenerate
