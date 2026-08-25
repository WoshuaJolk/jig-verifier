import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Interval

namespace Statements.Erdos404ConcreteFactorialValuation

open scoped BigOperators

def partialFactorialSum (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), (a i).factorial

/-- `2! + 3! = 8` has 2-adic valuation three. -/
abbrev statement : Prop :=
  padicValNat 2 (partialFactorialSum (fun i => i + 2) 1) = 3

theorem target : statement := sorry

end Statements.Erdos404ConcreteFactorialValuation
