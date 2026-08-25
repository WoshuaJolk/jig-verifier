import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Range

namespace Submissions.Erdos236RepresentationCountBound.Degenerate

def representationCount (n : ℕ) : ℕ :=
  ((List.range (Nat.log2 n + 1)).filter
    (fun k => Nat.Prime (n - 2 ^ k))).length

/-- Must-fail control: proves only a vacuous implication, not `statement`. -/
theorem proof :
    False → ∀ n : ℕ, representationCount n ≤ Nat.log2 n + 1 :=
  False.elim

end Submissions.Erdos236RepresentationCountBound.Degenerate
