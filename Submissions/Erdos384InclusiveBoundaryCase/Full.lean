import Mathlib

namespace Submissions.Erdos384InclusiveBoundaryCase.Full

theorem proof :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose 4 2 ∧ 2 * p ≤ 4 := by
  refine ⟨2, ?_⟩
  norm_num [Nat.choose]

end Submissions.Erdos384InclusiveBoundaryCase.Full
