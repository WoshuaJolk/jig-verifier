import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Interval

namespace Submissions.Erdos932FirstSmoothGapWitness.Degenerate

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- Must-fail control: adds an impossible hypothesis. -/
theorem proof :
    False →
      2 ≤ ((Finset.Ioo ((3 : ℕ).nth Nat.Prime) ((4 : ℕ).nth Nat.Prime)).filter
        (fun m => maxPrimeFac m <
          (4 : ℕ).nth Nat.Prime - (3 : ℕ).nth Nat.Prime)).card :=
  False.elim

end Submissions.Erdos932FirstSmoothGapWitness.Degenerate
