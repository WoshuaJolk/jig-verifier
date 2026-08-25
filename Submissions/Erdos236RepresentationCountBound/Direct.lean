import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Range

namespace Submissions.Erdos236RepresentationCountBound.Direct

def representationCount (n : ℕ) : ℕ :=
  ((List.range (Nat.log2 n + 1)).filter
    (fun k => Nat.Prime (n - 2 ^ k))).length

theorem proof : ∀ n : ℕ, representationCount n ≤ Nat.log2 n + 1 := by
  intro n
  simp only [representationCount]
  simpa using List.length_filter_le
    (fun k => decide (Nat.Prime (n - 2 ^ k)))
    (List.range (Nat.log2 n + 1))

end Submissions.Erdos236RepresentationCountBound.Direct
