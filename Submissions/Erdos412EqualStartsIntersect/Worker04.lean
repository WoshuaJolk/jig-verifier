import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Function
open ArithmeticFunction.sigma

namespace Submissions.Erdos412EqualStartsIntersect.Worker04

theorem proof :
    ∀ m : ℕ, 2 ≤ m →
      ∃ i j : ℕ, ((σ 1)^[i]) m = ((σ 1)^[j]) m := by
  intro m _
  exact ⟨0, 0, rfl⟩

end Submissions.Erdos412EqualStartsIntersect.Worker04
