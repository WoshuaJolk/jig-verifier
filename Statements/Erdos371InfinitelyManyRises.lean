import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card

namespace Statements.Erdos371InfinitelyManyRises

def largestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- The set of indices at which the largest prime factor rises is infinite. -/
abbrev statement : Prop :=
  {n : ℕ | largestPrimeFactor (n + 1) >
    largestPrimeFactor n}.Infinite

theorem target : statement := sorry

end Statements.Erdos371InfinitelyManyRises
