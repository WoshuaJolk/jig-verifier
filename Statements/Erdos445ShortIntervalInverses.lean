import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos445ShortIntervalInverses

open Filter

def HasInversePair (c : ℝ) (p n : ℕ) : Prop :=
  ∃ a b : ℕ,
    n < a ∧ (a : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    n < b ∧ (b : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    a * b ≡ 1 [MOD p]

/-- Erdős Problem 445. -/
abbrev statement : Prop :=
  ∀ c : ℝ, c > 1 / 2 →
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ n : ℕ, HasInversePair c p n

theorem target : statement := sorry

end Statements.Erdos445ShortIntervalInverses
