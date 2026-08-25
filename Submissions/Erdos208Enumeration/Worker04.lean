import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.PrimeCounting

namespace Submissions.Erdos208Enumeration.Worker04

noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

theorem proof :
    StrictMono squarefreeNumber ∧
      Set.range squarefreeNumber = {n : ℕ | Squarefree n} := by
  have hInf : Set.Infinite {n : ℕ | Squarefree n} :=
    Nat.infinite_setOfPred_prime.mono fun _ hn => hn.squarefree
  exact ⟨Nat.nth_strictMono hInf, Nat.range_nth_of_infinite hInf⟩

end Submissions.Erdos208Enumeration.Worker04
