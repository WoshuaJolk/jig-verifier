import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree

namespace Statements.Erdos145SquarefreeSequenceStrictMono

private theorem squarefree_infinite : Set.Infinite {n : ℕ | Squarefree n} :=
  Set.Infinite.mono (fun _ hp ↦ hp.squarefree) Nat.infinite_setOfPred_prime

noncomputable abbrev squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

/-- The sequence used in Erdős Problem 145 is strictly increasing, so all
of its consecutive natural-number gaps are positive. -/
abbrev statement : Prop :=
  StrictMono squarefreeNumber ∧
    ∀ n : ℕ, 0 < squarefreeNumber (n + 1) - squarefreeNumber n

theorem target : statement := sorry

end Statements.Erdos145SquarefreeSequenceStrictMono
