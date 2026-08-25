import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos404FactorialSumValuations

open Filter
open scoped BigOperators

def partialFactorialSum (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), (a i).factorial

/-- The infinite-sequence question in Erdős problem 404. -/
abbrev statement : Prop :=
  ∃ p : ℕ, p.Prime ∧
    ∃ a : ℕ → ℕ,
      (∀ i, 1 ≤ a i) ∧ StrictMono a ∧
        Tendsto (fun k => padicValNat p (partialFactorialSum a k))
          atTop atTop

theorem target : statement := sorry

end Statements.Erdos404FactorialSumValuations
