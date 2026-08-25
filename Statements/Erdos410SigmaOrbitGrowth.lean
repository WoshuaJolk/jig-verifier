import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos410SigmaOrbitGrowth

open ArithmeticFunction

/-- Every nontrivial sum-of-divisors orbit is strictly increasing and grows
at least linearly in the number of iterations. -/
abbrev statement : Prop :=
  ∀ n > 1,
    StrictMono (fun k : ℕ => (sigma 1)^[k] n) ∧
      ∀ k : ℕ, n + k ≤ (sigma 1)^[k] n

theorem target : statement := sorry

end Statements.Erdos410SigmaOrbitGrowth
