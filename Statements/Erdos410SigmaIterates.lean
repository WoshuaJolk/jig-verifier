import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos410SigmaIterates

open ArithmeticFunction Filter

/-- Erdős Problem 410: every nontrivial sum-of-divisors orbit has
unbounded exponential growth rate. -/
abbrev statement : Prop :=
  ∀ n > 1,
    Tendsto
      (fun k : ℕ => (((sigma 1)^[k] n : ℕ) : ℝ) ^ (1 / (k : ℝ)))
      atTop atTop

theorem target : statement := sorry

end Statements.Erdos410SigmaIterates
