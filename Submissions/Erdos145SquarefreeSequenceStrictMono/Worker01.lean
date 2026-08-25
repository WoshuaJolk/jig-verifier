import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
namespace Submissions.Erdos145SquarefreeSequenceStrictMono.Worker01
private theorem squarefree_infinite : Set.Infinite {n : ℕ | Squarefree n} := Set.Infinite.mono (fun _ hp ↦ hp.squarefree) Nat.infinite_setOfPred_prime
noncomputable abbrev squarefreeNumber (n : ℕ) : ℕ := Nat.nth Squarefree n
theorem proof : StrictMono squarefreeNumber ∧ ∀ n : ℕ, 0 < squarefreeNumber (n+1) - squarefreeNumber n := by
 have hm : StrictMono squarefreeNumber := Nat.nth_strictMono squarefree_infinite
 refine ⟨hm,fun n ↦ ?_⟩
 exact Nat.sub_pos_iff_lt.mpr (hm (Nat.lt_succ_self n))
end Submissions.Erdos145SquarefreeSequenceStrictMono.Worker01
