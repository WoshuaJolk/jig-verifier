import Mathlib.Data.Nat.Factorial.Basic

namespace Submissions.Erdos393FirstTwoSolutions.Worker09Middle

def IsConsecutiveProductFactorial (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ a : ℕ, 1 ≤ a ∧ n.factorial = a * (a + 1)

theorem proof :
    IsConsecutiveProductFactorial 2 ∧
      IsConsecutiveProductFactorial 3 := by
  constructor
  · refine ⟨by decide, 1, by decide, by decide⟩
  · refine ⟨by decide, 2, by decide, by decide⟩

end Submissions.Erdos393FirstTwoSolutions.Worker09Middle
