import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos409SigmaOrbitFour

open scoped ArithmeticFunction.sigma

def step (n : ℕ) : ℕ := σ 1 n - 1

/-- The nontrivial orbit `4 → 6 → 11` reaches a prime in two steps. -/
abbrev statement : Prop :=
  ((step)^[1]) 4 = 6 ∧ ((step)^[2]) 4 = 11 ∧
    (((step)^[2]) 4).Prime

theorem target : statement := sorry

end Statements.Erdos409SigmaOrbitFour
