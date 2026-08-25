import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos68FactorialTailBound

/-- The complete outer tail after row `m`, when scaled by `m!`, is at most
`(m+1)/m²`, hence strictly less than one. -/
abbrev statement : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    let f : ℕ → ℝ := fun k =>
      1 / (((m + k + 1).factorial - 1 : ℕ) : ℝ)
    Summable f ∧
      0 ≤ (m.factorial : ℝ) * ∑' k, f k ∧
      (m.factorial : ℝ) * ∑' k, f k ≤
        (m + 1 : ℝ) / m ^ 2 ∧
      (m + 1 : ℝ) / m ^ 2 < 1

theorem target : statement := sorry

end Statements.Erdos68FactorialTailBound
