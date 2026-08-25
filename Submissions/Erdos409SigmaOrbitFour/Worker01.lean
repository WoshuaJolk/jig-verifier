import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace Submissions.Erdos409SigmaOrbitFour.Worker01

open scoped ArithmeticFunction.sigma

def step (n : ℕ) : ℕ := σ 1 n - 1

theorem proof :
    ((step)^[1]) 4 = 6 ∧ ((step)^[2]) 4 = 11 ∧
      (((step)^[2]) 4).Prime := by
  decide

end Submissions.Erdos409SigmaOrbitFour.Worker01
