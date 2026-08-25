import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter
open scoped Pointwise

namespace Statements.Erdos124ShiftedPowerCompleteness

/-- Sums of distinct powers `d^i` whose exponents satisfy `k ≤ i`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/-- The open shifted-powers part of Erdős Problem 124. -/
abbrev statement : Prop :=
  ∀ k ≠ 0, ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) →
    1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ →
    D.gcd id = 1 →
    ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k

theorem target : statement := sorry

end Statements.Erdos124ShiftedPowerCompleteness
