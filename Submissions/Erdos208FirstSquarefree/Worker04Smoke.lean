import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.PrimeCounting

namespace Submissions.Erdos208FirstSquarefree.Worker04Smoke

noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

theorem proof : Squarefree (squarefreeNumber 0) := by
  have hInf : Set.Infinite {n : ℕ | Squarefree n} :=
    Nat.infinite_setOfPred_prime.mono fun _ hn => hn.squarefree
  exact Nat.nth_mem_of_infinite hInf 0

end Submissions.Erdos208FirstSquarefree.Worker04Smoke
