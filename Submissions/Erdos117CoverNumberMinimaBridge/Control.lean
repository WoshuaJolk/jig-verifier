import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117CoverNumberMinimaBridge.Control

/-- Must-fail anti-restatement control: the published statement is hidden
behind an additional false premise. -/
theorem proof :
    False →
      ∀ (A B : Set ℕ),
        A.Nonempty →
        B.Nonempty →
        (∀ a ∈ A, ∃ b ∈ B, b ≤ a) →
        (∀ b ∈ B, ∃ a ∈ A, a ≤ b) →
        sInf A = sInf B := by
  intro h
  exact h.elim

end Submissions.Erdos117CoverNumberMinimaBridge.Control
