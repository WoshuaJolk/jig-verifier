import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Interval

namespace Statements.Erdos932FirstSmoothGapWitness

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- The prime gap from 7 to 11 contains the two gap-smooth integers 8 and 9. -/
abbrev statement : Prop :=
  2 ≤ ((Finset.Ioo ((3 : ℕ).nth Nat.Prime) ((4 : ℕ).nth Nat.Prime)).filter
    (fun m => maxPrimeFac m <
      (4 : ℕ).nth Nat.Prime - (3 : ℕ).nth Nat.Prime)).card

theorem target : statement := sorry

end Statements.Erdos932FirstSmoothGapWitness
