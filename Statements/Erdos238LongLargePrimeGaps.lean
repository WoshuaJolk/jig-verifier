import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Real

namespace Statements.Erdos238LongLargePrimeGaps

/-- The gap between the `n`th and `(n+1)`st primes. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- Erdős Problem 238: arbitrary fixed lower bounds on prime gaps occur in blocks of more than `c₁ log x` consecutive primes below every sufficiently large `x`. -/
abbrev statement : Prop :=
  ∀ (c₁ : ℝ), c₁ > 0 → ∀ (c₂ : ℝ), c₂ > 0 →
    ∀ᶠ (x : ℝ) in atTop, ∃ k : ℕ,
      c₁ * log x < k ∧
        ∃ f : Fin k → ℕ, ∃ m : ℕ,
          (∀ i, f i ≤ x ∧ f i = (m + i.1).nth Nat.Prime) ∧
          ∀ i : Fin (k - 1), c₂ < primeGap (m + i.1)

theorem target : statement := sorry

end Statements.Erdos238LongLargePrimeGaps
