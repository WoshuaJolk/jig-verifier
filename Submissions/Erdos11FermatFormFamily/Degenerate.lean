import Mathlib.Data.Nat.Squarefree

namespace Submissions.Erdos11FermatFormFamily.Degenerate

/-- Deliberately weakened by an impossible extra hypothesis. -/
theorem proof :
    ∀ l : ℕ, 0 < l → l = 0 →
      ∃ k m : ℕ, Squarefree k ∧ 2 ^ l + 1 = k + 2 ^ m := by
  intro l hl hzero
  subst l
  simp at hl

end Submissions.Erdos11FermatFormFamily.Degenerate
