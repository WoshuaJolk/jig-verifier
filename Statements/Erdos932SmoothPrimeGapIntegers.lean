import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Interval

namespace Statements.Erdos932SmoothPrimeGapIntegers

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- Erdős problem 932. -/
abbrev statement : Prop :=
  {r : ℕ |
    2 ≤ ((Finset.Ioo (r.nth Nat.Prime) (r.succ.nth Nat.Prime)).filter
      (fun m => maxPrimeFac m <
        r.succ.nth Nat.Prime - r.nth Nat.Prime)).card}.Infinite

theorem target : statement := sorry

end Statements.Erdos932SmoothPrimeGapIntegers
