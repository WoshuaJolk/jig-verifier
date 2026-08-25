import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Submissions.Erdos400FeasiblePair.Worker04Smoke

theorem proof :
    ∃ a : Fin 2 → ℕ,
      (∏ i, Nat.factorial (a i)) ∣ Nat.factorial 0 ∧
      (∑ i, a i) = 2 := by
  refine ⟨![1, 1], ?_⟩
  decide

end Submissions.Erdos400FeasiblePair.Worker04Smoke
