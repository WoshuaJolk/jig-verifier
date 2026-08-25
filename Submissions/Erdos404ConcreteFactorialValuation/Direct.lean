import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Interval

namespace Submissions.Erdos404ConcreteFactorialValuation.Direct

open scoped BigOperators

def partialFactorialSum (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), (a i).factorial

theorem proof :
    padicValNat 2 (partialFactorialSum (fun i => i + 2) 1) = 3 := by
  decide +kernel

end Submissions.Erdos404ConcreteFactorialValuation.Direct
