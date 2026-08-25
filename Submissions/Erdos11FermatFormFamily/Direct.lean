import Mathlib.Data.Nat.Squarefree

namespace Submissions.Erdos11FermatFormFamily.Direct

theorem proof :
    ∀ l : ℕ, 0 < l →
      ∃ k m : ℕ, Squarefree k ∧ 2 ^ l + 1 = k + 2 ^ m := by
  intro l _
  exact ⟨1, l, squarefree_one, by simp [Nat.add_comm]⟩

end Submissions.Erdos11FermatFormFamily.Direct
