import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos409SigmaIterationTerminates

open scoped ArithmeticFunction.sigma

def step (n : ℕ) : ℕ :=
  σ 1 n - 1

/-- Erdős Problem 409, sigma variant: every positive nontrivial orbit under
`n ↦ σ(n)-1` eventually reaches a prime. -/
abbrev statement : Prop :=
  ∀ n : ℕ, n > 1 → ∃ i : ℕ, ((step)^[i]) n |>.Prime

theorem target : statement := sorry

end Statements.Erdos409SigmaIterationTerminates
