import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.PrimeCounting

namespace Submissions.Erdos208FirstSquarefree.Worker04Degenerate

noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

theorem proof : False → Squarefree (squarefreeNumber 0) :=
  False.elim

end Submissions.Erdos208FirstSquarefree.Worker04Degenerate
