import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Interval

namespace Submissions.Erdos404ConcreteFactorialValuation.Degenerate

open scoped BigOperators

def partialFactorialSum (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), (a i).factorial

/-- Must-fail control: adds an impossible hypothesis. -/
theorem proof :
    False →
      padicValNat 2 (partialFactorialSum (fun i => i + 2) 1) = 3 :=
  False.elim

end Submissions.Erdos404ConcreteFactorialValuation.Degenerate
