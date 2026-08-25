import Mathlib.NumberTheory.PrimeCounting

namespace Submissions.Erdos855ZeroArgumentBoundary.Worker03Identity

theorem proof :
    ∀ x : ℕ,
      Nat.primeCounting (x + 0) ≤
        Nat.primeCounting x + Nat.primeCounting 0 := by
  intro x
  simp

end Submissions.Erdos855ZeroArgumentBoundary.Worker03Identity
