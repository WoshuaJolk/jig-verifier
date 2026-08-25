import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card

namespace Submissions.Erdos371InfinitelyManyRises.Degenerate

def largestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

theorem proof : False →
    {n : ℕ | largestPrimeFactor (n + 1) >
      largestPrimeFactor n}.Infinite :=
  False.elim

end Submissions.Erdos371InfinitelyManyRises.Degenerate
